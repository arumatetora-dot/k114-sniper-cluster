#include <bits/stdc++.h>
#include <gmp.h>
#include <gmpxx.h>

using namespace std;
using u64  = uint64_t;
using i64  = long long;
using i128 = __int128_t;
using u128 = unsigned __int128;

i128 parse_i128(const string& s) {
    i128 res = 0; for (char c : s) if (isdigit(c)) res = res * 10 + (c - '0'); return res;
}

string format_i128(i128 val) {
    if (val == 0) return "0";
    bool neg = val < 0; if (neg) val = -val;
    string s = ""; while (val > 0) { s += (char)('0' + (val % 10)); val /= 10; }
    if (neg) s += '-'; reverse(s.begin(), s.end()); return s;
}

mpz_class to_mpz(i128 val) {
    unsigned long lo = (unsigned long)(val & 0xFFFFFFFFFFFFFFFFULL);
    unsigned long hi = (unsigned long)((u128)val >> 64);
    mpz_class res = hi; res <<= 64; res += lo; return res;
}

inline i64 mod_inv64(i64 a, i64 mod) {
    if (mod <= 1) return 0; a %= mod; if (a < 0) a += mod;
    i64 b = mod, u = 1, v = 0;
    while (b) { i64 t = a / b; a -= t * b; swap(a, b); u -= t * v; swap(u, v); }
    u %= mod; if (u < 0) u += mod; return u;
}

alignas(64) static const u64 P_LIST[16] = {
    1000000007ULL, 1000000009ULL, 1000000021ULL, 1000000033ULL,
    1000000087ULL, 1000000093ULL, 1000000097ULL, 1000000103ULL,
    1000000123ULL, 1000000181ULL, 1000000207ULL, 1000000223ULL,
    1000000241ULL, 1000000271ULL, 1000000289ULL, 1000000297ULL
};

inline bool is_qr_fast(i128 y, i128 u, u64 P) {
    u64 y_mod = (u64)(y % P), u_mod = (u64)(u % P);
    u64 y3 = (u64)((u128)y_mod * y_mod % P * y_mod % P);
    u64 u3 = (u64)((u128)u_mod * u_mod % P * u_mod % P);
    i64 V = (4LL * (i64)y3 - 456LL - (i64)u3) % (i64)P;
    if (V < 0) V += P;
    u64 div = (3 * u_mod) % P; if (div == 0) return true;
    u64 S = (u64)((u128)V * mod_inv64(div, P) % P);
    if (S == 0) return true;
    u64 r = 1, base = S, exp = (P - 1) >> 1;
    while (exp > 0) {
        if (exp & 1) r = (u64)((u128)r * base % P);
        base = (u64)((u128)base * base % P);
        exp >>= 1;
    }
    return r == 1;
}

int main(int argc, char** argv) {
    if (argc < 4) {
        cerr << "Usage: " << argv[0] << " <u_start> <u_end> <k_steps>" << endl;
        return 1;
    }
    i128 u_start = parse_i128(argv[1]);
    i128 u_end   = parse_i128(argv[2]);
    u64 k_steps  = stoull(argv[3]);

    cout << "Scanning range: u=[" << format_i128(u_start) << ", " << format_i128(u_end) << "], k_steps=" << k_steps << endl;

    for (i128 u = u_start; u <= u_end; ++u) {
        i64 r12 = (i64)(u % 12);
        if (r12 != 2 && r12 != 5 && r12 != 11) continue;
        if (u % 4 == 0 || u % 361 == 0) continue;

        for (u64 k = 1; k <= k_steps; ++k) {
            i128 y = (i128)k * u + 1; // 代表軌道
            bool pass = true;
            for (int pi = 0; pi < 16; ++pi) {
                if (!is_qr_fast(y, u, P_LIST[pi])) { pass = false; break; }
            }
            if (!pass) continue;

            mpz_class my = to_mpz(y), mu = to_mpz(u);
            mpz_class A = 4 * (((my * my * my) - 114) / mu) - (mu * mu * mu);
            if (A > 0 && A % 3 == 0) {
                mpz_class S2 = A / 3, s, rem;
                mpz_sqrtrem(s.get_mpz_t(), rem.get_mpz_t(), S2.get_mpz_t());
                if (rem == 0 && s > mu && (s - mu) % 2 == 0) {
                    mpz_class x = (s - mu) / 2, z = (s + mu) / 2;
                    cout << "🚨 [FOUND] X=" << x.get_str() << ", Y=" << my.get_str() << ", Z=-" << z.get_str() << " (u=" << format_i128(u) << ")" << endl;
                }
            }
        }
    }
    return 0;
}
