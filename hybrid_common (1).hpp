#ifndef HYBRID_COMMON_HPP
#define HYBRID_COMMON_HPP

#include <algorithm>
#include <cerrno>
#include <csignal>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

#include <arpa/inet.h>
#include <netdb.h>
#include <netinet/in.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <sys/types.h>
#include <unistd.h>

#include <openssl/crypto.h>
#include <openssl/evp.h>
#include <openssl/rand.h>
#include <cstddef>

typedef uint64_t u64;
typedef uint32_t u32;
typedef uint8_t u8;
typedef unsigned __int128 u128;

struct Fp { u64 v[8]; };
struct Pt { Fp X, Z; };

static const int NPR = 74;
static const u32 ROUNDS = 32;
static int PR[NPR];
static u64 PM[8];
static u64 NPRIME;
static Fp FZERO, FONE, FR2, FINV4, FTWO;
static u64 EXP_INV[8], EXP_LEG[8];

static void mul_small(u64* array_pointer, u64 multiplier) {
    u64 carry = 0;
    for (int i = 0; i < 8; i++) {
        u128 temporary = (u128)array_pointer[i] * multiplier + carry;
        array_pointer[i] = (u64)temporary;
        carry = (u64)(temporary >> 64);
    }
}

static bool ge_p(const u64* array_pointer) {
    for (int i = 7; i >= 0; i--) {
        if (array_pointer[i] > PM[i]) return true;
        if (array_pointer[i] < PM[i]) return false;
    }
    return true;
}

static void sub_p(u64* array_pointer) {
    u64 borrow = 0;
    for (int i = 0; i < 8; i++) {
        u128 temporary = (u128)array_pointer[i] - PM[i] - borrow;
        array_pointer[i] = (u64)temporary;
        borrow = (u64)((temporary >> 64) & 1);
    }
}

static void fadd(Fp& result, const Fp& operand_a, const Fp& operand_b) {
    u128 carry = 0;
    for (int i = 0; i < 8; i++) {
        carry += (u128)operand_a.v[i] + operand_b.v[i];
        result.v[i] = (u64)carry;
        carry >>= 64;
    }
    if (carry || ge_p(result.v)) sub_p(result.v);
}

static void fsub(Fp& result, const Fp& operand_a, const Fp& operand_b) {
    u64 borrow = 0;
    for (int i = 0; i < 8; i++) {
        u128 temporary = (u128)operand_a.v[i] - operand_b.v[i] - borrow;
        result.v[i] = (u64)temporary;
        borrow = (u64)((temporary >> 64) & 1);
    }
    if (borrow) {
        u128 carry = 0;
        for (int i = 0; i < 8; i++) {
            carry += (u128)result.v[i] + PM[i];
            result.v[i] = (u64)carry;
            carry >>= 64;
        }
    }
}

static void fmul(Fp& result, const Fp& operand_a, const Fp& operand_b) {
    u64 temp_array[10] = {0};
    for (int i = 0; i < 8; i++) {
        u128 carry = 0;
        for (int j = 0; j < 8; j++) {
            carry += (u128)operand_a.v[j] * operand_b.v[i] + temp_array[j];
            temp_array[j] = (u64)carry;
            carry >>= 64;
        }
        carry += temp_array[8];
        temp_array[8] = (u64)carry;
        temp_array[9] = (u64)(carry >> 64);
        u64 multiplier_value = temp_array[0] * NPRIME;
        carry = (u128)multiplier_value * PM[0] + temp_array[0];
        carry >>= 64;
        for (int j = 1; j < 8; j++) {
            carry += (u128)multiplier_value * PM[j] + temp_array[j];
            temp_array[j - 1] = (u64)carry;
            carry >>= 64;
        }
        carry += temp_array[8];
        temp_array[7] = (u64)carry;
        carry >>= 64;
        temp_array[8] = temp_array[9] + (u64)carry;
    }
    for (int i = 0; i < 8; i++) result.v[i] = temp_array[i];
    if (temp_array[8] || ge_p(result.v)) sub_p(result.v);
}

static void fsqr(Fp& result, const Fp& operand_a) { fmul(result, operand_a, operand_a); }

static bool fiszero(const Fp& operand_a) {
    u64 output_mask = 0;
    for (int i = 0; i < 8; i++) output_mask |= operand_a.v[i];
    return output_mask == 0;
}

static bool feq(const Fp& operand_a, const Fp& operand_b) {
    u64 output_mask = 0;
    for (int i = 0; i < 8; i++) output_mask |= operand_a.v[i] ^ operand_b.v[i];
    return output_mask == 0;
}

static void fpow(Fp& result, const Fp& operand_a, const u64* exponent) {
    Fp result_val = FONE;
    for (int i = 511; i >= 0; i--) {
        fsqr(result_val, result_val);
        if ((exponent[i >> 6] >> (i & 63)) & 1) fmul(result_val, result_val, operand_a);
    }
    result = result_val;
}

static void fpow_small(Fp& result, const Fp& operand_a, u64 exponent_val) {
    int top_bit = 63;
    while (top_bit > 0 && !((exponent_val >> top_bit) & 1)) top_bit--;
    Fp result_val = FONE;
    for (int i = top_bit; i >= 0; i--) {
        fsqr(result_val, result_val);
        if ((exponent_val >> i) & 1) fmul(result_val, result_val, operand_a);
    }
    result = result_val;
}

static void finv(Fp& result, const Fp& operand_a) { fpow(result, operand_a, EXP_INV); }

static int fleg(const Fp& operand_a) {
    if (fiszero(operand_a)) return 0;
    Fp result;
    fpow(result, operand_a, EXP_LEG);
    return feq(result, FONE) ? 1 : -1;
}

static Fp tomont(const Fp& operand_a) {
    Fp result;
    fmul(result, operand_a, FR2);
    return result;
}

static Fp frommont(const Fp& operand_a) {
    Fp one, result;
    memset(&one, 0, sizeof one);
    one.v[0] = 1;
    fmul(result, operand_a, one);
    return result;
}

static void init_params() {
    int count = 0;
    for (int prime_candidate = 3; prime_candidate <= 373; prime_candidate += 2) {
        bool is_prime = true;
        for (int divisor = 3; divisor * divisor <= prime_candidate; divisor += 2)
            if (prime_candidate % divisor == 0) { is_prime = false; break; }
        if (is_prime) PR[count++] = prime_candidate;
    }
    PR[count++] = 587;
    memset(PM, 0, sizeof PM);
    PM[0] = 4;
    for (int i = 0; i < NPR; i++) mul_small(PM, (u64)PR[i]);
    PM[0] -= 1;
    u64 inverse = 1;
    for (int i = 0; i < 7; i++) inverse *= 2 - PM[0] * inverse;
    NPRIME = (u64)0 - inverse;
    Fp x_coord;
    memset(&x_coord, 0, sizeof x_coord);
    x_coord.v[0] = 1;
    for (int i = 0; i < 1024; i++) {
        fadd(x_coord, x_coord, x_coord);
        if (i == 511) FONE = x_coord;
    }
    FR2 = x_coord;
    memset(&FZERO, 0, sizeof FZERO);
    fadd(FTWO, FONE, FONE);
    memcpy(EXP_INV, PM, sizeof PM);
    EXP_INV[0] -= 2;
    for (int i = 0; i < 8; i++) EXP_LEG[i] = (PM[i] >> 1) | (i < 7 ? PM[i + 1] << 63 : 0);
    Fp four;
    fadd(four, FTWO, FTWO);
    finv(FINV4, four);
}

static void rnd_bytes(u8* byte_array, size_t length) {
    static FILE* file_pointer = nullptr;
    if (!file_pointer) {
        file_pointer = fopen("/dev/urandom", "rb");
        if (!file_pointer) { fprintf(stderr, "Khong mo duoc /dev/urandom\n"); exit(1); }
    }
    if (fread(byte_array, 1, length, file_pointer) != length) { fprintf(stderr, "Loi doc /dev/urandom\n"); exit(1); }
}

static Fp rnd_fp() {
    Fp result;
    for (;;) {
        rnd_bytes((u8*)result.v, 64);
        result.v[7] &= 0x7FFFFFFFFFFFFFFFULL;
        if (!ge_p(result.v)) return tomont(result);
    }
}

static void rnd_priv(int8_t* priv_array) {
    for (int i = 0; i < NPR; i++) {
        u8 byte_val;
        do rnd_bytes(&byte_val, 1); while (byte_val >= 253);
        priv_array[i] = (int8_t)((int)(byte_val % 11) - 5);
    }
}

static bool pt_inf(const Pt& point_p) { return fiszero(point_p.Z); }

static Fp a24_of(const Fp& curve_a) {
    Fp temp, result;
    fadd(temp, curve_a, FTWO);
    fmul(result, temp, FINV4);
    return result;
}

static void xdbl(Pt& result, const Pt& point_p, const Fp& curve_a24) {
    Fp temp_zero, temp_one, temp_two, temp_three;
    fadd(temp_zero, point_p.X, point_p.Z);
    fsqr(temp_zero, temp_zero);
    fsub(temp_one, point_p.X, point_p.Z);
    fsqr(temp_one, temp_one);
    fsub(temp_two, temp_zero, temp_one);
    fmul(temp_three, curve_a24, temp_two);
    fadd(temp_three, temp_three, temp_one);
    fmul(result.X, temp_zero, temp_one);
    fmul(result.Z, temp_two, temp_three);
}

static void xadd(Pt& result, const Pt& point_p, const Pt& point_q, const Pt& point_d) {
    Fp temp_zero, temp_one, temp_two, temp_three, variable_u, variable_v;
    fsub(temp_zero, point_q.X, point_q.Z);
    fadd(temp_one, point_p.X, point_p.Z);
    fmul(temp_zero, temp_zero, temp_one);
    fadd(temp_two, point_q.X, point_q.Z);
    fsub(temp_three, point_p.X, point_p.Z);
    fmul(temp_one, temp_two, temp_three);
    fadd(variable_u, temp_zero, temp_one);
    fsqr(variable_u, variable_u);
    fsub(variable_v, temp_zero, temp_one);
    fsqr(variable_v, variable_v);
    Pt point_other;
    fmul(point_other.X, point_d.Z, variable_u);
    fmul(point_other.Z, point_d.X, variable_v);
    result = point_other;
}

static void xmul(Pt& result, const Pt& point_p, const u64* scalar_key, const Fp& curve_a24) {
    Pt point_r0, point_r1 = point_p;
    point_r0.X = FONE;
    point_r0.Z = FZERO;
    int top_bit = -1;
    for (int i = 511; i >= 0; i--)
        if ((scalar_key[i >> 6] >> (i & 63)) & 1) { top_bit = i; break; }
    if (top_bit < 0) { result = point_r0; return; }
    for (int i = top_bit; i >= 0; i--) {
        if ((scalar_key[i >> 6] >> (i & 63)) & 1) {
            xadd(point_r0, point_r0, point_r1, point_p);
            xdbl(point_r1, point_r1, curve_a24);
        } else {
            xadd(point_r1, point_r0, point_r1, point_p);
            xdbl(point_r0, point_r0, curve_a24);
        }
    }
    result = point_r0;
}

static void isogeny(Fp& curve_a, Pt& point_q, const Pt& point_k, int degree_l) {
    Fp curve_a24 = a24_of(curve_a);
    int degree_d = (degree_l - 1) / 2;
    std::vector<Pt> point_vector(degree_d + 2);
    point_vector[1] = point_k;
    if (degree_d >= 2) xdbl(point_vector[2], point_k, curve_a24);
    for (int i = 3; i <= degree_d; i++) xadd(point_vector[i], point_vector[i - 1], point_k, point_vector[i - 2]);
    Fp product_plus = FONE, product_minus = FONE, term_plus = FONE, term_minus = FONE, x_minus, x_plus;
    fsub(x_minus, point_q.X, point_q.Z);
    fadd(x_plus, point_q.X, point_q.Z);
    for (int i = 1; i <= degree_d; i++) {
        Fp sum_val, diff_val, variable_u, variable_v, weight_one, weight_two;
        fadd(sum_val, point_vector[i].X, point_vector[i].Z);
        fsub(diff_val, point_vector[i].X, point_vector[i].Z);
        fmul(product_plus, product_plus, sum_val);
        fmul(product_minus, product_minus, diff_val);
        fmul(variable_u, x_minus, sum_val);
        fmul(variable_v, x_plus, diff_val);
        fadd(weight_one, variable_u, variable_v);
        fsub(weight_two, variable_u, variable_v);
        fmul(term_plus, term_plus, weight_one);
        fmul(term_minus, term_minus, weight_two);
    }
    Fp a_plus, a_minus, numerator, denominator, numerator_val, denominator_val, inverse_val;
    fadd(a_plus, curve_a, FTWO);
    fsub(a_minus, curve_a, FTWO);
    fpow_small(numerator, a_plus, (u64)degree_l);
    fpow_small(denominator, a_minus, (u64)degree_l);
    for (int i = 0; i < 3; i++) {
        fsqr(product_plus, product_plus);
        fsqr(product_minus, product_minus);
    }
    fmul(numerator, numerator, product_plus);
    fmul(denominator, denominator, product_minus);
    fadd(numerator_val, numerator, denominator);
    fsub(denominator_val, numerator, denominator);
    finv(inverse_val, denominator_val);
    fmul(curve_a, numerator_val, inverse_val);
    fadd(curve_a, curve_a, curve_a);
    Fp temp_two, temp_three;
    fsqr(temp_two, term_plus);
    fsqr(temp_three, term_minus);
    fmul(point_q.X, point_q.X, temp_two);
    fmul(point_q.Z, point_q.Z, temp_three);
}

static void action(Fp& output_buffer, const Fp& curve_a0, const int8_t* priv_e0) {
    int8_t exponent[NPR];
    memcpy(exponent, priv_e0, NPR);
    Fp curve_a = curve_a0;
    for (;;) {
        bool has_any = false;
        for (int i = 0; i < NPR; i++)
            if (exponent[i]) { has_any = true; break; }
        if (!has_any) break;
        Fp x_coord = rnd_fp();
        Fp x_squared, temp, legendre_poly;
        fsqr(x_squared, x_coord);
        fmul(temp, curve_a, x_coord);
        fadd(temp, temp, x_squared);
        fadd(temp, temp, FONE);
        fmul(legendre_poly, temp, x_coord);
        int legendre_val = fleg(legendre_poly);
        if (legendre_val == 0) continue;
        std::vector<int> index_list;
        for (int i = 0; i < NPR; i++)
            if (exponent[i] != 0 && ((exponent[i] > 0) == (legendre_val > 0))) index_list.push_back(i);
        if (index_list.empty()) continue;
        bool in_subset[NPR];
        for (int i = 0; i < NPR; i++) in_subset[i] = false;
        for (size_t j = 0; j < index_list.size(); j++) in_subset[index_list[j]] = true;
        u64 scalar_key[8];
        memset(scalar_key, 0, sizeof scalar_key);
        scalar_key[0] = 4;
        for (int i = 0; i < NPR; i++)
            if (!in_subset[i]) mul_small(scalar_key, (u64)PR[i]);
        Fp curve_a24 = a24_of(curve_a);
        Pt point_p, point_q;
        point_p.X = x_coord;
        point_p.Z = FONE;
        xmul(point_q, point_p, scalar_key, curve_a24);
        std::vector<int> active_list = index_list;
        for (size_t idx = 0; idx < index_list.size(); idx++) {
            int i = index_list[idx];
            memset(scalar_key, 0, sizeof scalar_key);
            scalar_key[0] = 1;
            for (size_t j = 0; j < active_list.size(); j++)
                if (active_list[j] != i) mul_small(scalar_key, (u64)PR[active_list[j]]);
            curve_a24 = a24_of(curve_a);
            Pt point_r;
            xmul(point_r, point_q, scalar_key, curve_a24);
            if (pt_inf(point_r)) continue;
            isogeny(curve_a, point_q, point_r, PR[i]);
            exponent[i] = (int8_t)(exponent[i] - legendre_val);
            active_list.erase(std::find(active_list.begin(), active_list.end(), i));
        }
    }
    output_buffer = curve_a;
}

static bool validate(const Fp& curve_a) {
    Fp minus_two;
    fsub(minus_two, FZERO, FTWO);
    if (feq(curve_a, FTWO) || feq(curve_a, minus_two)) return false;
    Fp curve_a24 = a24_of(curve_a);
    for (int attempt_index = 0; attempt_index < 24; attempt_index++) {
        Fp x_coord = rnd_fp();
        Pt point_p, point_r;
        point_p.X = x_coord;
        point_p.Z = FONE;
        u64 scalar_key4[8];
        memset(scalar_key4, 0, sizeof scalar_key4);
        scalar_key4[0] = 4;
        xmul(point_r, point_p, scalar_key4, curve_a24);
        u64 divisor_array[8];
        memset(divisor_array, 0, sizeof divisor_array);
        divisor_array[0] = 1;
        for (int i = 0; i < NPR; i++) {
            u64 scalar_key[8];
            memset(scalar_key, 0, sizeof scalar_key);
            scalar_key[0] = 1;
            for (int j = 0; j < NPR; j++)
                if (j != i) mul_small(scalar_key, (u64)PR[j]);
            Pt point_q;
            xmul(point_q, point_r, scalar_key, curve_a24);
            if (!pt_inf(point_q)) {
                Pt point_t;
                u64 scalar_key_l[8];
                memset(scalar_key_l, 0, sizeof scalar_key_l);
                scalar_key_l[0] = (u64)PR[i];
                xmul(point_t, point_q, scalar_key_l, curve_a24);
                if (!pt_inf(point_t)) return false;
                mul_small(divisor_array, (u64)PR[i]);
            }
        }
        int bit_length = 0;
        for (int i = 511; i >= 0; i--)
            if ((divisor_array[i >> 6] >> (i & 63)) & 1) { bit_length = i + 1; break; }
        if (bit_length >= 259) return true;
    }
    return false;
}

static void fp_to_bytes(const Fp& operand_a, u8* output_buffer) {
    Fp result = frommont(operand_a);
    for (int i = 0; i < 8; i++)
        for (int b = 0; b < 8; b++) output_buffer[i * 8 + b] = (u8)(result.v[i] >> (8 * b));
}

static bool fp_from_bytes(const u8* input_buffer, Fp& operand_a) {
    Fp result;
    for (int i = 0; i < 8; i++) {
        u64 word_value = 0;
        for (int b = 0; b < 8; b++) word_value |= (u64)input_buffer[i * 8 + b] << (8 * b);
        result.v[i] = word_value;
    }
    if (ge_p(result.v)) return false;
    operand_a = tomont(result);
    return true;
}

namespace hqc {

using Bytes = std::vector<uint8_t>;
using Vec = std::vector<uint64_t>;

constexpr size_t N = 17669;
constexpr size_t WT = 66;
constexpr size_t MSG = 64;
constexpr size_t WORDS = (N + 63) / 64;
constexpr size_t NBYTES = (N + 7) / 8;
constexpr size_t TAG_BYTES = 32;
constexpr size_t RS_K = 64;
constexpr size_t RS_P = 74;
constexpr size_t RS_N = RS_K + RS_P;
constexpr size_t RM_LEN = 128;
constexpr size_t RM_DUP = 1;
constexpr size_t RM_BLOCK = RM_LEN * RM_DUP;
constexpr uint64_t LAST_MASK = (1ULL << (N % 64)) - 1ULL;

static_assert(N % 64 != 0, "N must not be a multiple of 64");
static_assert(RS_N * RM_BLOCK <= N, "ECC expansion must fit in N bits");

inline uint64_t rotl64(uint64_t x, unsigned n) {
    return (x << n) | (x >> (64 - n));
}

inline void keccak_f(uint64_t st[25]) {
    static const uint64_t RC[24] = {
        0x0000000000000001ULL, 0x0000000000008082ULL, 0x800000000000808aULL,
        0x8000000080008000ULL, 0x000000000000808bULL, 0x0000000080000001ULL,
        0x8000000080008081ULL, 0x8000000000008009ULL, 0x000000000000008aULL,
        0x0000000000000088ULL, 0x0000000080008009ULL, 0x000000008000000aULL,
        0x000000008000808bULL, 0x800000000000008bULL, 0x8000000000008089ULL,
        0x8000000000008003ULL, 0x8000000000008002ULL, 0x8000000000000080ULL,
        0x000000000000800aULL, 0x800000008000000aULL, 0x8000000080008081ULL,
        0x8000000000008080ULL, 0x0000000080000001ULL, 0x8000000080008008ULL};
    static const unsigned ROT[24] = {1,  3,  6,  10, 15, 21, 28, 36, 45, 55, 2,  14,
                                     27, 41, 56, 8,  25, 43, 62, 18, 39, 61, 20, 44};
    static const int PI[24] = {10, 7,  11, 17, 18, 3, 5,  16, 8,  21, 24, 4,
                               15, 23, 19, 13, 12, 2, 20, 14, 22, 9,  6,  1};
    for (int round = 0; round < 24; ++round) {
        uint64_t bc[5];
        for (int i = 0; i < 5; ++i) bc[i] = st[i] ^ st[i + 5] ^ st[i + 10] ^ st[i + 15] ^ st[i + 20];
        for (int i = 0; i < 5; ++i) {
            uint64_t t = bc[(i + 4) % 5] ^ rotl64(bc[(i + 1) % 5], 1);
            for (int j = 0; j < 25; j += 5) st[j + i] ^= t;
        }
        uint64_t t = st[1];
        for (int i = 0; i < 24; ++i) {
            int j = PI[i];
            uint64_t tmp = st[j];
            st[j] = rotl64(t, ROT[i]);
            t = tmp;
        }
        for (int j = 0; j < 25; j += 5) {
            for (int i = 0; i < 5; ++i) bc[i] = st[j + i];
            for (int i = 0; i < 5; ++i) st[j + i] ^= (~bc[(i + 1) % 5]) & bc[(i + 2) % 5];
        }
        st[0] ^= RC[round];
    }
}

class Shake256 {
public:
    static constexpr size_t RATE = 136;

    Shake256() : pos_(0), done_(false) { std::memset(st_, 0, sizeof st_); }

    Shake256& put(const uint8_t* d, size_t n) {
        for (size_t i = 0; i < n; ++i) {
            st_[pos_ >> 3] ^= static_cast<uint64_t>(d[i]) << (8 * (pos_ & 7));
            if (++pos_ == RATE) {
                keccak_f(st_);
                pos_ = 0;
            }
        }
        return *this;
    }
    Shake256& put(const Bytes& b) { return put(b.data(), b.size()); }
    Shake256& put(const std::string& s) {
        return put(reinterpret_cast<const uint8_t*>(s.data()), s.size());
    }

    void squeeze(uint8_t* out, size_t n) {
        if (!done_) finalize();
        for (size_t i = 0; i < n; ++i) {
            if (pos_ == RATE) {
                keccak_f(st_);
                pos_ = 0;
            }
            out[i] = static_cast<uint8_t>((st_[pos_ >> 3] >> (8 * (pos_ & 7))) & 0xFF);
            ++pos_;
        }
    }

    Bytes out(size_t n) {
        Bytes r(n);
        squeeze(r.data(), n);
        return r;
    }

private:
    void finalize() {
        st_[pos_ >> 3] ^= static_cast<uint64_t>(0x1F) << (8 * (pos_ & 7));
        st_[(RATE - 1) >> 3] ^= static_cast<uint64_t>(0x80) << (8 * ((RATE - 1) & 7));
        keccak_f(st_);
        pos_ = 0;
        done_ = true;
    }

    uint64_t st_[25];
    size_t pos_;
    bool done_;
};

inline uint32_t next32(Shake256& s) {
    uint8_t b[4];
    s.squeeze(b, 4);
    return static_cast<uint32_t>(b[0]) | (static_cast<uint32_t>(b[1]) << 8) |
           (static_cast<uint32_t>(b[2]) << 16) | (static_cast<uint32_t>(b[3]) << 24);
}

inline uint32_t rand_below(Shake256& s, uint32_t bound) {
    uint32_t th = (0u - bound) % bound;
    uint32_t r;
    do {
        r = next32(s);
    } while (r < th);
    return r % bound;
}

inline bool ct_equal(const uint8_t* a, const uint8_t* b, size_t n) {
    uint8_t acc = 0;
    for (size_t i = 0; i < n; ++i) acc |= static_cast<uint8_t>(a[i] ^ b[i]);
    return acc == 0;
}

inline bool ct_equal(const Bytes& a, const Bytes& b) {
    if (a.size() != b.size()) return false;
    return ct_equal(a.data(), b.data(), a.size());
}

inline Vec vec_zero() { return Vec(WORDS, 0); }

inline Vec vxor(const Vec& a, const Vec& b) {
    Vec r(WORDS);
    for (size_t i = 0; i < WORDS; ++i) r[i] = a[i] ^ b[i];
    return r;
}

inline bool getbit(const Vec& v, size_t i) { return (v[i >> 6] >> (i & 63)) & 1ULL; }

inline void setbit(Vec& v, size_t i) { v[i >> 6] |= 1ULL << (i & 63); }

inline size_t popcount(const Vec& v) {
    size_t c = 0;
    for (uint64_t w : v) c += static_cast<size_t>(__builtin_popcountll(w));
    return c;
}

inline Bytes vec_to_bytes(const Vec& v) {
    Bytes b(NBYTES);
    for (size_t i = 0; i < NBYTES; ++i) b[i] = static_cast<uint8_t>((v[i >> 3] >> (8 * (i & 7))) & 0xFF);
    return b;
}

inline Vec bytes_to_vec(const uint8_t* b) {
    Vec v(WORDS, 0);
    for (size_t i = 0; i < NBYTES; ++i) v[i >> 3] |= static_cast<uint64_t>(b[i]) << (8 * (i & 7));
    v[WORDS - 1] &= LAST_MASK;
    return v;
}

inline bool parse_vec(const Bytes& b, Vec& out) {
    if (b.size() != NBYTES) return false;
    if ((b[NBYTES - 1] >> (N % 8)) != 0) return false;
    out = bytes_to_vec(b.data());
    return true;
}

inline Vec mul(const Vec& a, const Vec& b) {
    const Vec* sp = &a;
    const Vec* dn = &b;
    if (popcount(a) > popcount(b)) std::swap(sp, dn);
    const uint64_t* d = dn->data();
    std::vector<uint64_t> acc(2 * WORDS + 1, 0);
    for (size_t w = 0; w < WORDS; ++w) {
        uint64_t bits = (*sp)[w];
        while (bits) {
            unsigned t = static_cast<unsigned>(__builtin_ctzll(bits));
            bits &= bits - 1;
            uint64_t* dst = acc.data() + w;
            if (t == 0) {
                for (size_t j = 0; j < WORDS; ++j) dst[j] ^= d[j];
            } else {
                const unsigned rt = 64 - t;
                for (size_t j = 0; j < WORDS; ++j) {
                    dst[j] ^= d[j] << t;
                    dst[j + 1] ^= d[j] >> rt;
                }
            }
        }
    }
    constexpr size_t SW = N >> 6;
    constexpr unsigned SB = N & 63;
    Vec r(WORDS);
    for (size_t j = 0; j < WORDS; ++j) {
        uint64_t hi = (acc[SW + j] >> SB) | (acc[SW + j + 1] << (64 - SB));
        r[j] = acc[j] ^ hi;
    }
    r[WORDS - 1] &= LAST_MASK;
    return r;
}

inline Vec sample_sparse(Shake256& s, size_t wt) {
    Vec v(WORDS, 0);
    size_t cnt = 0;
    while (cnt < wt) {
        uint32_t p = rand_below(s, static_cast<uint32_t>(N));
        uint64_t bit = 1ULL << (p & 63);
        uint64_t& w = v[p >> 6];
        if (w & bit) continue;
        w |= bit;
        ++cnt;
    }
    return v;
}

inline Vec random_sparse(const std::string& label) {
    Bytes seed(32);
    if (RAND_bytes(seed.data(), static_cast<int>(seed.size())) != 1)
        throw std::runtime_error("RAND_bytes failed");
    Shake256 sh;
    sh.put(label).put(seed);
    Vec v = sample_sparse(sh, WT);
    OPENSSL_cleanse(seed.data(), seed.size());
    return v;
}

inline Vec derive_h(const std::string& seed) {
    Shake256 sh;
    sh.put(std::string("hvec")).put(seed);
    Bytes b = sh.out(NBYTES);
    return bytes_to_vec(b.data());
}

struct GF {
    uint8_t ex[512];
    uint8_t lg[256];
    GF() {
        std::memset(ex, 0, sizeof ex);
        std::memset(lg, 0, sizeof lg);
        unsigned x = 1;
        for (unsigned i = 0; i < 255; ++i) {
            ex[i] = static_cast<uint8_t>(x);
            lg[x] = static_cast<uint8_t>(i);
            x <<= 1;
            if (x & 0x100) x ^= 0x11D;
        }
        for (unsigned i = 255; i < 512; ++i) ex[i] = ex[i - 255];
    }
};

inline const GF& gf() {
    static const GF g;
    return g;
}

inline uint8_t gmul(uint8_t a, uint8_t b) {
    if (!a || !b) return 0;
    const GF& g = gf();
    return g.ex[g.lg[a] + g.lg[b]];
}

inline uint8_t gdiv(uint8_t a, uint8_t b) {
    if (!a) return 0;
    const GF& g = gf();
    return g.ex[g.lg[a] + 255 - g.lg[b]];
}

inline uint8_t galpha(int e) { return gf().ex[((e % 255) + 255) % 255]; }

inline uint8_t gpow(uint8_t a, int e) {
    if (e == 0) return 1;
    if (!a) return 0;
    const GF& g = gf();
    return g.ex[(static_cast<int>(g.lg[a]) * e) % 255];
}

struct RsGen {
    uint8_t g[RS_P + 1];
    RsGen() {
        std::memset(g, 0, sizeof g);
        g[0] = 1;
        int deg = 0;
        for (size_t i = 0; i < RS_P; ++i) {
            uint8_t a = galpha(static_cast<int>(i));
            for (int j = deg + 1; j >= 0; --j) {
                uint8_t prev = j > 0 ? g[j - 1] : 0;
                g[j] = prev ^ gmul(a, g[j]);
            }
            ++deg;
        }
    }
};

inline const RsGen& rs_gen() {
    static const RsGen g;
    return g;
}

inline void rs_encode(const uint8_t* msg, uint8_t* cw) {
    const RsGen& G = rs_gen();
    uint8_t r[RS_P];
    std::memset(r, 0, sizeof r);
    for (int i = static_cast<int>(RS_K) - 1; i >= 0; --i) {
        uint8_t fb = msg[i] ^ r[RS_P - 1];
        for (size_t j = RS_P - 1; j > 0; --j) r[j] = r[j - 1] ^ gmul(fb, G.g[j]);
        r[0] = gmul(fb, G.g[0]);
    }
    std::memcpy(cw, r, RS_P);
    std::memcpy(cw + RS_P, msg, RS_K);
}

inline bool rs_syndromes(const uint8_t* cw, uint8_t* S) {
    bool any = false;
    for (size_t j = 0; j < RS_P; ++j) {
        uint8_t a = galpha(static_cast<int>(j));
        uint8_t acc = 0;
        for (int i = static_cast<int>(RS_N) - 1; i >= 0; --i) acc = gmul(acc, a) ^ cw[i];
        S[j] = acc;
        if (acc) any = true;
    }
    return any;
}

inline bool rs_decode(const uint8_t* in, uint8_t* msg) {
    uint8_t cw[RS_N];
    std::memcpy(cw, in, RS_N);
    uint8_t S[RS_P];
    if (rs_syndromes(cw, S)) {
        uint8_t C[RS_P + 1], B[RS_P + 1], T[RS_P + 1];
        std::memset(C, 0, sizeof C);
        std::memset(B, 0, sizeof B);
        C[0] = 1;
        B[0] = 1;
        int L = 0;
        int m = 1;
        uint8_t b = 1;
        for (int n = 0; n < static_cast<int>(RS_P); ++n) {
            uint8_t d = S[n];
            for (int i = 1; i <= L; ++i) d ^= gmul(C[i], S[n - i]);
            if (!d) {
                ++m;
                continue;
            }
            std::memcpy(T, C, sizeof C);
            uint8_t coef = gdiv(d, b);
            for (int i = 0; i + m <= static_cast<int>(RS_P); ++i) C[i + m] ^= gmul(coef, B[i]);
            if (2 * L <= n) {
                L = n + 1 - L;
                std::memcpy(B, T, sizeof B);
                b = d;
                m = 1;
            } else {
                ++m;
            }
        }
        if (L > static_cast<int>(RS_P / 2)) return false;
        int locs[RS_P];
        int nl = 0;
        for (int p = 0; p < static_cast<int>(RS_N); ++p) {
            uint8_t xi = galpha(255 - p);
            uint8_t acc = 0;
            for (int i = L; i >= 0; --i) acc = gmul(acc, xi) ^ C[i];
            if (!acc) {
                if (nl >= static_cast<int>(RS_P)) return false;
                locs[nl++] = p;
            }
        }
        if (nl != L) return false;
        uint8_t O[RS_P];
        for (size_t k = 0; k < RS_P; ++k) {
            uint8_t acc = 0;
            for (size_t i = 0; i <= k && i <= static_cast<size_t>(L); ++i) acc ^= gmul(C[i], S[k - i]);
            O[k] = acc;
        }
        for (int q = 0; q < nl; ++q) {
            int p = locs[q];
            uint8_t xi = galpha(255 - p);
            uint8_t om = 0;
            for (int k = static_cast<int>(RS_P) - 1; k >= 0; --k) om = gmul(om, xi) ^ O[k];
            uint8_t der = 0;
            for (int i = 1; i <= L; i += 2) der ^= gmul(C[i], gpow(xi, i - 1));
            if (!der) return false;
            cw[p] ^= gmul(galpha(p), gdiv(om, der));
        }
        if (rs_syndromes(cw, S)) return false;
    }
    std::memcpy(msg, cw + RS_P, RS_K);
    return true;
}

inline void rm_encode_byte(uint8_t b, Vec& v, size_t block) {
    unsigned a0 = b & 1u;
    unsigned a = static_cast<unsigned>(b) >> 1;
    for (unsigned x = 0; x < RM_LEN; ++x) {
        unsigned bit = a0 ^ static_cast<unsigned>(__builtin_parity(a & x));
        if (bit) {
            for (size_t d = 0; d < RM_DUP; ++d) setbit(v, block * RM_BLOCK + d * RM_LEN + x);
        }
    }
}

inline uint8_t rm_decode_block(const Vec& v, size_t block) {
    int T[RM_LEN];
    for (size_t x = 0; x < RM_LEN; ++x) {
        int sum = 0;
        for (size_t d = 0; d < RM_DUP; ++d)
            sum += 1 - 2 * static_cast<int>(getbit(v, block * RM_BLOCK + d * RM_LEN + x));
        T[x] = sum;
    }
    for (size_t len = 1; len < RM_LEN; len <<= 1) {
        for (size_t i = 0; i < RM_LEN; i += 2 * len) {
            for (size_t j = i; j < i + len; ++j) {
                int u = T[j];
                int w = T[j + len];
                T[j] = u + w;
                T[j + len] = u - w;
            }
        }
    }
    size_t best = 0;
    int bestabs = std::abs(T[0]);
    for (size_t i = 1; i < RM_LEN; ++i) {
        int av = std::abs(T[i]);
        if (av > bestabs) {
            bestabs = av;
            best = i;
        }
    }
    unsigned a0 = T[best] < 0 ? 1u : 0u;
    return static_cast<uint8_t>((best << 1) | a0);
}

inline Vec ecc_encode(const uint8_t* m) {
    uint8_t cw[RS_N];
    rs_encode(m, cw);
    Vec v = vec_zero();
    for (size_t i = 0; i < RS_N; ++i) rm_encode_byte(cw[i], v, i);
    return v;
}

inline bool ecc_decode(const Vec& v, uint8_t* m) {
    uint8_t cw[RS_N];
    for (size_t i = 0; i < RS_N; ++i) cw[i] = rm_decode_block(v, i);
    return rs_decode(cw, m);
}


struct Noise {
    Vec r1;
    Vec r2;
    Vec e;
};

inline Noise derive_noise(const Bytes& pkc, const Bytes& shared, const Bytes& sb, const Bytes& pks) {
    Shake256 sh;
    sh.put(std::string("nested_noise")).put(pkc).put(shared).put(sb).put(pks);
    Noise n;
    n.r1 = sample_sparse(sh, WT);
    n.r2 = sample_sparse(sh, WT);
    n.e = sample_sparse(sh, WT);
    return n;
}

struct Cipher {
    Vec u;
    Vec v;
};

inline Cipher hqc_encrypt(const Vec& h, const Vec& s, const Bytes& pkc, const Noise& n) {
    Vec c = ecc_encode(pkc.data());
    Cipher out;
    out.u = vxor(n.r1, mul(h, n.r2));
    out.v = vxor(vxor(c, n.e), mul(s, n.r2));
    return out;
}

inline Bytes auth_tag(const Bytes& shared, const Bytes& pkc, const Bytes& ub, const Bytes& vb) {
    Shake256 sh;
    sh.put(std::string("auth_tag")).put(shared).put(pkc).put(ub).put(vb);
    return sh.out(TAG_BYTES);
}

inline Bytes confirm_tag(const Bytes& shared, const Bytes& pkc, const Bytes& tag) {
    Shake256 sh;
    sh.put(std::string("confirm")).put(shared).put(pkc).put(tag);
    return sh.out(TAG_BYTES);
}

inline Bytes session_key(const Bytes& shared, const Bytes& pkc, const Bytes& ub, const Bytes& vb) {
    Shake256 sh;
    sh.put(std::string("CSIDH-HQC-SK")).put(shared).put(pkc).put(ub).put(vb);
    return sh.out(32);
}

inline std::string to_hex(const uint8_t* p, size_t n) {
    static const char* d = "0123456789abcdef";
    std::string s;
    s.reserve(2 * n);
    for (size_t i = 0; i < n; ++i) {
        s.push_back(d[p[i] >> 4]);
        s.push_back(d[p[i] & 15]);
    }
    return s;
}

struct Fd {
    int fd;
    explicit Fd(int f = -1) : fd(f) {}
    ~Fd() {
        if (fd >= 0) ::close(fd);
    }
    Fd(const Fd&) = delete;
    Fd& operator=(const Fd&) = delete;
};

inline void set_timeouts(int fd) {
    timeval tv;
    tv.tv_sec = 60;
    tv.tv_usec = 0;
    setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);
    setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof tv);
}

inline bool send_all(int fd, const uint8_t* p, size_t n) {
    while (n > 0) {
        ssize_t r = ::send(fd, p, n, MSG_NOSIGNAL);
        if (r < 0) {
            if (errno == EINTR) continue;
            return false;
        }
        if (r == 0) return false;
        p += r;
        n -= static_cast<size_t>(r);
    }
    return true;
}

inline bool recv_all(int fd, uint8_t* p, size_t n) {
    while (n > 0) {
        ssize_t r = ::recv(fd, p, n, 0);
        if (r < 0) {
            if (errno == EINTR) continue;
            return false;
        }
        if (r == 0) return false;
        p += r;
        n -= static_cast<size_t>(r);
    }
    return true;
}

inline bool send_frame(int fd, const Bytes& b) {
    uint8_t hdr[4];
    uint32_t n = static_cast<uint32_t>(b.size());
    hdr[0] = static_cast<uint8_t>(n >> 24);
    hdr[1] = static_cast<uint8_t>(n >> 16);
    hdr[2] = static_cast<uint8_t>(n >> 8);
    hdr[3] = static_cast<uint8_t>(n);
    return send_all(fd, hdr, 4) && send_all(fd, b.data(), b.size());
}

inline bool recv_frame(int fd, Bytes& out, size_t maxlen) {
    uint8_t hdr[4];
    if (!recv_all(fd, hdr, 4)) return false;
    size_t n = (static_cast<size_t>(hdr[0]) << 24) | (static_cast<size_t>(hdr[1]) << 16) |
               (static_cast<size_t>(hdr[2]) << 8) | static_cast<size_t>(hdr[3]);
    if (n > maxlen) return false;
    out.assign(n, 0);
    return recv_all(fd, out.data(), n);
}

inline int make_listener(uint16_t port) {
    int fd = ::socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return -1;
    int one = 1;
    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
    sockaddr_in addr;
    std::memset(&addr, 0, sizeof addr);
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_ANY);
    addr.sin_port = htons(port);
    if (::bind(fd, reinterpret_cast<sockaddr*>(&addr), sizeof addr) != 0 || ::listen(fd, 1) != 0) {
        ::close(fd);
        return -1;
    }
    return fd;
}

inline int connect_to(const char* host, const char* port) {
    addrinfo hints;
    std::memset(&hints, 0, sizeof hints);
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    addrinfo* res = nullptr;
    if (getaddrinfo(host, port, &hints, &res) != 0) return -1;
    int fd = -1;
    for (addrinfo* p = res; p != nullptr; p = p->ai_next) {
        fd = ::socket(p->ai_family, p->ai_socktype, p->ai_protocol);
        if (fd < 0) continue;
        if (::connect(fd, p->ai_addr, p->ai_addrlen) == 0) break;
        ::close(fd);
        fd = -1;
    }
    freeaddrinfo(res);
    return fd;
}

inline bool parse_port(const char* s, uint16_t& out) {
    char* end = nullptr;
    errno = 0;
    long v = std::strtol(s, &end, 10);
    if (errno != 0 || end == s || *end != '\0' || v < 1 || v > 65535) return false;
    out = static_cast<uint16_t>(v);
    return true;
}

}

#endif
