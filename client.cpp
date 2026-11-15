#include "hybrid_common.hpp"

namespace {

int fail(const char* why) {
    std::fprintf(stderr, "session aborted: %s\n", why);
    return 1;
}

int run(const std::string& seed, const char* host, const char* port) {
    using namespace hqc;

    init_params();

    Fd conn(connect_to(host, port));
    if (conn.fd < 0) return fail("cannot connect");
    set_timeouts(conn.fd);

    Bytes sb, pks;
    if (!recv_frame(conn.fd, sb, NBYTES) || !recv_frame(conn.fd, pks, 64))
        return fail("receive public key failed");

    Vec s;
    if (!parse_vec(sb, s)) return fail("malformed s");
    Fp pk_S_fp;
    if (pks.size() != 64 || !fp_from_bytes(pks.data(), pk_S_fp) || !validate(pk_S_fp))
        return fail("invalid server CSIDH public key");

    Vec h = derive_h(seed);

    int8_t sk_C[NPR];
    rnd_priv(sk_C);
    Fp pk_C_fp, shared_fp;
    action(pk_C_fp, FZERO, sk_C);
    action(shared_fp, pk_S_fp, sk_C);
    OPENSSL_cleanse(sk_C, sizeof sk_C);

    uint8_t pk_C_bytes[64];
    uint8_t shared_csidh[64];
    fp_to_bytes(pk_C_fp, pk_C_bytes);
    fp_to_bytes(shared_fp, shared_csidh);

    Bytes pkc(pk_C_bytes, pk_C_bytes + 64);
    Bytes shared(shared_csidh, shared_csidh + 64);
    Bytes sk;

    int rc = 0;
    const char* why = nullptr;

    do {
        Noise nz = derive_noise(pkc, shared, sb, pks);
        Cipher ct = hqc_encrypt(h, s, pkc, nz);
        Bytes ub = vec_to_bytes(ct.u);
        Bytes vb = vec_to_bytes(ct.v);
        Bytes tag = auth_tag(shared, pkc, ub, vb);

        if (!send_frame(conn.fd, ub) || !send_frame(conn.fd, vb) || !send_frame(conn.fd, tag)) {
            why = "send failed";
            break;
        }

        Bytes conf;
        if (!recv_frame(conn.fd, conf, TAG_BYTES)) {
            why = "no confirmation received";
            break;
        }
        Bytes expect = confirm_tag(shared, pkc, tag);
        if (!ct_equal(conf, expect)) {
            why = "confirmation mismatch";
            break;
        }

        sk = session_key(shared, pkc, ub, vb);
        std::printf("AES-256 session key = %s\n", to_hex(sk.data(), sk.size()).c_str());
        std::fflush(stdout);
    } while (false);

    if (why) rc = fail(why);

    OPENSSL_cleanse(pk_C_bytes, sizeof pk_C_bytes);
    OPENSSL_cleanse(shared_csidh, sizeof shared_csidh);
    OPENSSL_cleanse(shared.data(), shared.size());
    OPENSSL_cleanse(pkc.data(), pkc.size());
    if (!sk.empty()) OPENSSL_cleanse(sk.data(), sk.size());
    return rc;
}

}

int main(int argc, char** argv) {
    if (argc < 2 || argc > 4) {
        std::fprintf(stderr, "usage: %s <seed> [host] [port]\n", argv[0]);
        return 2;
    }
    const char* host = argc >= 3 ? argv[2] : "127.0.0.1";
    const char* port = argc == 4 ? argv[3] : "9000";
    uint16_t pn = 0;
    if (!hqc::parse_port(port, pn)) {
        std::fprintf(stderr, "invalid port\n");
        return 2;
    }
    std::signal(SIGPIPE, SIG_IGN);
    try {
        return run(argv[1], host, port);
    } catch (const std::exception& e) {
        std::fprintf(stderr, "error: %s\n", e.what());
        return 1;
    }
}
