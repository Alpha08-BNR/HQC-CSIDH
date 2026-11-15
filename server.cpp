#include "hybrid_common.hpp"

namespace {

int fail(const char* why) {
    std::fprintf(stderr, "session aborted: %s\n", why);
    return 1;
}

int run(const std::string& seed, uint16_t port) {
    using namespace hqc;

    init_params();

    Vec h = derive_h(seed);
    Vec y = random_sparse("yvec");
    Vec x = random_sparse("xvec");
    Vec s = vxor(x, mul(h, y));
    Bytes sb = vec_to_bytes(s);

    int8_t sk_S[NPR];
    rnd_priv(sk_S);
    Fp pk_S_fp;
    action(pk_S_fp, FZERO, sk_S);
    uint8_t pk_S[64];
    fp_to_bytes(pk_S_fp, pk_S);
    Bytes pks(pk_S, pk_S + 64);

    Fd listener(make_listener(port));
    if (listener.fd < 0) {
        OPENSSL_cleanse(sk_S, sizeof sk_S);
        return fail("cannot listen on port");
    }
    std::fprintf(stderr, "listening on port %u\n", static_cast<unsigned>(port));

    Fd conn(::accept(listener.fd, nullptr, nullptr));
    if (conn.fd < 0) {
        OPENSSL_cleanse(sk_S, sizeof sk_S);
        return fail("accept failed");
    }
    set_timeouts(conn.fd);

    int rc = 0;
    const char* why = nullptr;

    uint8_t pk_C[64];
    uint8_t shared_csidh[64];
    Bytes pkc, shared, sk;
    std::memset(pk_C, 0, sizeof pk_C);
    std::memset(shared_csidh, 0, sizeof shared_csidh);

    do {
        if (!send_frame(conn.fd, sb) || !send_frame(conn.fd, pks)) {
            why = "send public key failed";
            break;
        }

        Bytes ub, vb, tag;
        if (!recv_frame(conn.fd, ub, NBYTES) || !recv_frame(conn.fd, vb, NBYTES) ||
            !recv_frame(conn.fd, tag, TAG_BYTES)) {
            why = "receive failed";
            break;
        }
        if (ub.size() != NBYTES || vb.size() != NBYTES || tag.size() != TAG_BYTES) {
            why = "bad frame size";
            break;
        }

        Vec u, v;
        if (!parse_vec(ub, u) || !parse_vec(vb, v)) {
            why = "malformed ciphertext";
            break;
        }

        Vec filt = vxor(v, mul(y, u));
        if (!ecc_decode(filt, pk_C)) {
            why = "ECC decoding failed";
            break;
        }

        Fp pk_C_fp;
        if (!fp_from_bytes(pk_C, pk_C_fp) || !validate(pk_C_fp)) {
            why = "invalid client CSIDH public key";
            break;
        }

        Fp shared_fp;
        action(shared_fp, pk_C_fp, sk_S);
        fp_to_bytes(shared_fp, shared_csidh);

        pkc.assign(pk_C, pk_C + 64);
        shared.assign(shared_csidh, shared_csidh + 64);

        Noise nz = derive_noise(pkc, shared, sb, pks);
        Cipher re = hqc_encrypt(h, s, pkc, nz);
        Bytes u2 = vec_to_bytes(re.u);
        Bytes v2 = vec_to_bytes(re.v);
        bool ok_u = ct_equal(u2, ub);
        bool ok_v = ct_equal(v2, vb);
        if (!(ok_u & ok_v)) {
            why = "re-encryption check failed";
            break;
        }

        Bytes tag2 = auth_tag(shared, pkc, ub, vb);
        if (!ct_equal(tag2, tag)) {
            why = "auth tag check failed";
            break;
        }

        Bytes conf = confirm_tag(shared, pkc, tag);
        if (!send_frame(conn.fd, conf)) {
            why = "send confirmation failed";
            break;
        }

        sk = session_key(shared, pkc, ub, vb);
        std::printf("AES-256 session key = %s\n", to_hex(sk.data(), sk.size()).c_str());
        std::fflush(stdout);
    } while (false);

    if (why) rc = fail(why);

    OPENSSL_cleanse(sk_S, sizeof sk_S);
    OPENSSL_cleanse(pk_C, sizeof pk_C);
    OPENSSL_cleanse(shared_csidh, sizeof shared_csidh);
    if (!shared.empty()) OPENSSL_cleanse(shared.data(), shared.size());
    if (!pkc.empty()) OPENSSL_cleanse(pkc.data(), pkc.size());
    if (!sk.empty()) OPENSSL_cleanse(sk.data(), sk.size());
    if (!x.empty()) OPENSSL_cleanse(x.data(), x.size() * sizeof(uint64_t));
    if (!y.empty()) OPENSSL_cleanse(y.data(), y.size() * sizeof(uint64_t));
    return rc;
}

}

int main(int argc, char** argv) {
    if (argc < 2 || argc > 3) {
        std::fprintf(stderr, "usage: %s <seed> [port]\n", argv[0]);
        return 2;
    }
    uint16_t port = 9000;
    if (argc == 3 && !hqc::parse_port(argv[2], port)) {
        std::fprintf(stderr, "invalid port\n");
        return 2;
    }
    std::signal(SIGPIPE, SIG_IGN);
    try {
        return run(argv[1], port);
    } catch (const std::exception& e) {
        std::fprintf(stderr, "error: %s\n", e.what());
        return 1;
    }
}
