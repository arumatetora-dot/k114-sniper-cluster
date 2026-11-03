%%writefile hyper_sniper.cpp
#include <bits/stdc++.h>
#include <gmp.h>
#include <gmpxx.h>
#include <NTL/ZZ.h>
#include <NTL/mat_ZZ.h>
#include <NTL/LLL.h>
#include <hiredis/hiredis.h>
#include <unistd.h>

using namespace std;
using namespace NTL;

using u64  = uint64_t;
using i64  = long long;
using i128 = __int128_t;
using u128 = unsigned __int128;

static constexpr long double PI_VAL = 3.14159265358979323846L;

i128 parse_i128(const string& s) {
    i128 res = 0; for (char c : s) if (isdigit(c)) res = res * 10 + (c - '0'); return res;
}

string format_i128(i128 val) {
    if (val == 0) return "0";
    bool neg = val < 0; if (neg) val = -val;
    string s = ""; while (val > 0) { s += (char)('0' + (val % 10)); val /= 10; }
    string res = ""; int cnt = 0;
    for (int i = 0; i < (int)s.size(); ++i) { if (cnt > 0 && cnt % 3 == 0) res += ','; res += s[i]; cnt++; }
    if (neg) res += '-'; reverse(res.begin(), res.end()); return res;
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

bool is_prime_u64(u64 n) {
    if (n < 2) return false;
    static const u64 small_p[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
    for (u64 p : small_p) { if (n == p) return true; if (n % p == 0) return false; }
    u64 d = n - 1; int s = 0; while ((d & 1) == 0) { d >>= 1; ++s; }
    static const u64 bases[] = {2, 325, 9375, 28178, 450775, 9780504, 1795265022};
    for (u64 a : bases) {
        if (a % n == 0) continue;
        u64 x = 1, base = a % n, exp = d;
        while (exp > 0) { if (exp & 1) x = (u64)((u128)x * base % n); base = (u64)((u128)base * base % n); exp >>= 1; }
        if (x == 1 || x == n - 1) continue;
        bool comp = true;
        for (int r = 1; r < s; ++r) {
            x = (u64)((u128)x * x % n);
            if (x == n - 1) { comp = false; break; }
        }
        if (comp) return false;
    }
    return true;
}

u64 pollard_rho64_safe(u64 n) {
    if ((n & 1) == 0) return 2;
    for (u64 c = 1; c < 200; ++c) {
        u64 y = 2, m = 128, g = 1, r = 1, q = 1, ys = 2, x = 2;
        auto f = [&](u64 v) -> u64 { return ((u128)v * v + c) % n; };
        while (g == 1) {
            x = y; for (u64 i = 0; i < r; ++i) y = f(y);
            u64 k = 0;
            while (k < r && g == 1) {
                ys = y; u64 lim = min(m, r - k);
                for (u64 i = 0; i < lim; ++i) {
                    y = f(y); u64 diff = (x > y) ? (x - y) : (y - x);
                    q = (u64)((u128)q * diff % n);
                }
                g = std::gcd(q, n); k += m;
            }
            r <<= 1;
            if (r > 1000000ULL) break;
        }
        if (g == n) {
            do { ys = f(ys); u64 diff = (x > ys) ? (x - ys) : (ys - x); g = std::gcd(diff, n); } while (g == 1);
        }
        if (g > 1 && g < n) return g;
    }
    return 0;
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

static i64 dlog_pow3(i64 g, i64 h, int S, i64 p) {
    if (S <= 0 || p <= 1) return 0; i64 x = 0, cur_g = g % p, cur_h = h % p, pow3_i = 1;
    for (int i = 0; i < S; ++i) {
        i64 exp = 1; for (int e = 0; e < S - i - 1; ++e) exp *= 3;
        i64 gh = 1, b1 = cur_g, e1 = exp;
        while (e1 > 0) { if (e1 & 1) gh = (u64)((u128)gh * b1 % p); b1 = (u64)((u128)b1 * b1 % p); e1 >>= 1; }
        i64 hh = 1, b2 = cur_h, e2 = exp;
        while (e2 > 0) { if (e2 & 1) hh = (u64)((u128)hh * b2 % p); b2 = (u64)((u128)b2 * b2 % p); e2 >>= 1; }
        int d = 0; i64 val = 1;
        for (; d < 3; ++d) { if (val == hh) break; val = (u64)((u128)val * gh % p); }
        if (d == 3) return -1;
        x += d * pow3_i;
        if (d) {
            i64 gd = 1, bg = cur_g, eg = d;
            while (eg > 0) { if (eg & 1) gd = (u64)((u128)gd * bg % p); bg = (u64)((u128)bg * bg % p); eg >>= 1; }
            cur_h = (u64)((u128)cur_h * mod_inv64(gd, p) % p);
        }
        i64 n_g = 1, b3 = cur_g, e3 = 3;
        while (e3 > 0) { if (e3 & 1) n_g = (u64)((u128)n_g * b3 % p); b3 = (u64)((u128)b3 * b3 % p); e3 >>= 1; }
        cur_g = n_g; pow3_i *= 3;
    }
    return x;
}

static vector<i64> cube_roots_mod_prime(i64 a, i64 p) {
    if (p <= 1) return {};
    a %= p; if (a < 0) a += p;
    if (p == 2) return (a == 0) ? vector<i64>{0} : vector<i64>{};
    if (p == 3) return {};
    if (p % 3 == 2) {
        i64 phi = p - 1, inv3 = mod_inv64(3 % phi, phi);
        i64 r = 1, b = a, e = inv3;
        while (e > 0) { if (e & 1) r = (u64)((u128)r * b % p); b = (u64)((u128)b * b % p); e >>= 1; }
        return {r};
    }
    i64 chk = 1, b = a, e = (p - 1) / 3;
    while (e > 0) { if (e & 1) chk = (u64)((u128)chk * b % p); b = (u64)((u128)b * b % p); e >>= 1; }
    if (chk != 1) return {};
    i64 m = p - 1; int s = 0; 
    while (m > 0 && m % 3 == 0) { m /= 3; ++s; }
    if (m <= 0) return {};

    i64 base_b = 2; bool found_b = false;
    for (int t = 0; t < 200; ++t, ++base_b) {
        i64 c_chk = 1, bb = base_b, ee = (p - 1) / 3;
        while (ee > 0) { if (ee & 1) c_chk = (u64)((u128)c_chk * bb % p); bb = (u64)((u128)bb * bb % p); ee >>= 1; }
        if (c_chk != 1) { found_b = true; break; }
    }
    if (!found_b) return {};

    i64 c = 1, bb = base_b, ee = m;
    while (ee > 0) { if (ee & 1) c = (u64)((u128)c * bb % p); bb = (u64)((u128)bb * bb % p); ee >>= 1; }
    i64 x = 0;
    if (m == 1) {
        i64 base = (u64)((u128)c * c % p * c % p);
        i64 j = (s > 1) ? dlog_pow3(base, a, s - 1, p) : 0;
        if (j < 0) return {};
        i64 cj = 1, bc = c, ec = j;
        while (ec > 0) { if (ec & 1) cj = (u64)((u128)cj * bc % p); bc = (u64)((u128)bc * bc % p); ec >>= 1; }
        x = cj;
    } else {
        i64 t = mod_inv64(3 % m, m), k = (3 * t - 1) / m;
        i64 x0 = 1, bx = a, ex = t;
        while (ex > 0) { if (ex & 1) x0 = (u64)((u128)x0 * bx % p); bx = (u64)((u128)bx * bx % p); ex >>= 1; }
        i64 d = 1, bd = a, ed = m;
        while (ed > 0) { if (ed & 1) d = (u64)((u128)d * bd % p); bd = (u64)((u128)bd * bd % p); ed >>= 1; }
        i64 target = (k == 1) ? mod_inv64(d, p) : mod_inv64((u64)((u128)d * d % p), p);
        i64 base = (u64)((u128)c * c % p * c % p);
        i64 j = (s > 1) ? dlog_pow3(base, target, s - 1, p) : 0;
        if (j < 0) return {};
        i64 cj = 1, bc = c, ec = j;
        while (ec > 0) { if (ec & 1) cj = (u64)((u128)cj * bc % p); bc = (u64)((u128)bc * bc % p); ec >>= 1; }
        x = (u64)((u128)x0 * cj % p);
    }
    i64 p3 = 1; for (int i = 0; i < s - 1; ++i) p3 *= 3;
    i64 omega = 1, bo = c, eo = p3;
    while (eo > 0) { if (eo & 1) omega = (u64)((u128)omega * bo % p); bo = (u64)((u128)bo * bo % p); eo >>= 1; }
    return {x, (i64)((u128)x * omega % p), (i64)((u128)x * omega % p * omega % p)};
}

static vector<i64> lift_roots(i64 a, i64 p, int e, const vector<i64>& roots_p) {
    if (p <= 1) return {};
    vector<i64> res;
    for (i64 r : roots_p) {
        i64 cur = r % p, pk = p;
        for (int k = 1; k < e; ++k) {
            i64 modnext = pk * p;
            i64 cur3 = (u64)((u128)cur * cur % modnext * cur % modnext);
            i64 f = (cur3 + modnext - (a % modnext)) % modnext;
            i64 deriv = (3 * (i128)(cur % p) * (cur % p)) % p;
            cur = cur + ((p - ((f / pk) % p) * mod_inv64(deriv, p) % p) % p) * pk; pk = modnext;
        }
        res.push_back(cur % pk);
    }
    return res;
}

static vector<i128> crt_combine128(const vector<i128>& A, i128 m1, const vector<i64>& B, i64 m2) {
    if (m1 <= 0 || m2 <= 0) return {};
    vector<i128> C; C.reserve(A.size() * B.size());
    i64 inv = mod_inv64((i64)(m1 % m2), m2); i128 m = m1 * m2;
    for (i128 r1 : A) for (i64 r2 : B) {
        i64 diff = (i64)((r2 - (r1 % m2)) % m2); if (diff < 0) diff += m2;
        i64 t = (i64)((i128)diff * inv % m2);
        C.push_back((r1 + m1 * t) % m);
    }
    return C;
}

struct AngleMetrics {
    double phi_deg, psi_deg, tan2_phi, lambda_val;
};

AngleMetrics calc_angle_metrics(i128 u, i128 y) {
    long double eta = (long double)y / (long double)u;
    long double s_over_u = sqrtl((4.0L * eta * eta * eta - 1.0L) / 3.0L);
    long double w_over_u = 0.5L * (s_over_u + 2.0L * eta - 1.0L);
    long double v2_over_u = 0.5L * (s_over_u - (2.0L * eta - 1.0L));
    if (v2_over_u < 1e-18L) v2_over_u = 1e-18L;
    long double tan2_phi = 1.0L / v2_over_u;
    long double phi_deg  = atanl(sqrtl(tan2_phi)) * 180.0L / PI_VAL;
    long double cos_psi  = v2_over_u / w_over_u;
    if (cos_psi > 1.0L) cos_psi = 1.0L;
    long double psi_deg  = acosl(cos_psi) * 180.0L / PI_VAL;
    long double lambda_val = w_over_u / (1.0L + v2_over_u);
    return {(double)phi_deg, (double)psi_deg, (double)tan2_phi, (double)lambda_val};
}

int main(int argc, char** argv) {
    int pid = getpid();
    string host   = (argc >= 2) ? argv[1] : "127.0.0.1";
    int port      = (argc >= 3) ? stoi(argv[2]) : 6389;
    string pass   = (argc >= 4) ? argv[3] : "";
    string stream = (argc >= 5) ? argv[4] : "sym18_test";

    redisContext* c = redisConnect(host.c_str(), port);
    if (!c || c->err) return 1;

    const int SIEVE_MAX = 650000;
    vector<bool> is_p(SIEVE_MAX + 1, true);
    vector<int> forbidden_primes, valid_primes;
    unordered_map<i64, vector<i64>> small_root_cache;

    for (int p = 2; p <= SIEVE_MAX; ++p) {
        if (!is_p[p]) continue;
        for (long long j = 1LL * p * p; j <= SIEVE_MAX; j += p) is_p[j] = false;
        if (p == 3) continue;
        if (p == 2 || p == 19) {
            valid_primes.push_back(p); small_root_cache[p] = {0};
        } else if (p % 3 == 2) {
            valid_primes.push_back(p);
            i64 phi = p - 1, inv3 = mod_inv64(3 % phi, phi);
            i64 r = 1, b = 114 % p, e = inv3;
            while (e > 0) { if (e & 1) r = (u64)((u128)r * b % p); b = (u64)((u128)b * b % p); e >>= 1; }
            small_root_cache[p] = {r};
        } else {
            i64 chk = 1, b = 114 % p, e = (p - 1) / 3;
            while (e > 0) { if (e & 1) chk = (u64)((u128)chk * b % p); b = (u64)((u128)b * b % p); e >>= 1; }
            if (chk == 1) {
                valid_primes.push_back(p); small_root_cache[p] = cube_roots_mod_prime(114 % p, p);
            } else {
                forbidden_primes.push_back(p);
            }
        }
    }

    while (true) {
        redisReply* chk_stop = (redisReply*)redisCommand(c, "GET %s:stop", stream.c_str());
        if (chk_stop && chk_stop->type == REDIS_REPLY_STRING) { freeReplyObject(chk_stop); break; }
        if (chk_stop) freeReplyObject(chk_stop);

        redisReply* rep = (redisReply*)redisCommand(c, "LPOP %s:task_queue", stream.c_str());
        if (!rep || rep->type == REDIS_REPLY_NIL) {
            if (rep) freeReplyObject(rep);
            usleep(200000);
            continue;
        }
        string task = rep->str; freeReplyObject(rep);
        if (task == "STOP") break;

        stringstream ss(task); string tok;
        getline(ss, tok, ','); u64 t_id = stoull(tok);
        getline(ss, tok, ','); i128 u_start = parse_i128(tok);
        getline(ss, tok, ','); i128 u_end   = parse_i128(tok);
        getline(ss, tok, ','); u64 k_steps  = stoull(tok);

        size_t L = (size_t)(u_end - u_start + 1);
        vector<uint8_t> alive(L, 0);
        vector<i128> rem_u(L);
        vector<vector<pair<i64, int>>> small_facs(L);

        for (size_t i = 0; i < L; ++i) {
            i128 u = u_start + i; rem_u[i] = u;
            i64 r12 = (i64)(u % 12);
            if ((r12 == 2 || r12 == 5 || r12 == 11) && (u % 4 != 0) && (u % 361 != 0)) alive[i] = 1;
        }

        for (int p : forbidden_primes) {
            u64 rem = (u64)(u_start % (i128)p);
            size_t first = (rem == 0) ? 0 : (p - rem);
            for (size_t i = first; i < L; i += p) alive[i] = 0;
        }

        for (int p : valid_primes) {
            u64 rem = (u64)(u_start % (i128)p);
            size_t first = (rem == 0) ? 0 : (p - rem);
            for (size_t i = first; i < L; i += p) {
                if (!alive[i]) continue;
                int e = 0;
                while (rem_u[i] % p == 0) { rem_u[i] /= p; ++e; }
                if ((p == 2 || p == 19) && e > 1) { alive[i] = 0; continue; }
                small_facs[i].push_back({p, e});
            }
        }

        u64 chunk_u_scanned = L, chunk_valid_u = 0, chunk_y_checked = 0, chunk_euler_surv = 0;
        bool lattice_logged_this_chunk = false;

        for (size_t i = 0; i < L; ++i) {
            if (!alive[i]) continue;
            i128 u = u_start + i, cof = rem_u[i];
            vector<pair<i64, int>> large_facs;
            if (cof > 1) {
                if (cof <= 0xFFFFFFFFFFFFFFFFULL) {
                    u64 c64 = (u64)cof;
                    if (is_prime_u64(c64)) {
                        if (c64 % 3 == 1) {
                            i64 chk = 1, bb = 114 % c64, ee = (c64 - 1) / 3;
                            while (ee > 0) { if (ee & 1) chk = (u64)((u128)chk * bb % c64); bb = (u64)((u128)bb * bb % c64); ee >>= 1; }
                            if (chk != 1) continue;
                        }
                        large_facs.push_back({(i64)c64, 1});
                    } else {
                        u64 d = pollard_rho64_safe(c64);
                        if (d <= 1 || d >= c64) continue;
                        u64 p1 = d, p2 = c64 / d;
                        if (p1 <= 1 || p2 <= 1) continue;
                        if (p1 > p2) swap(p1, p2);
                        if (p1 == p2) {
                            if (p1 == 2 || p1 == 19) continue;
                            large_facs.push_back({(i64)p1, 2});
                        } else {
                            large_facs.push_back({(i64)p1, 1}); large_facs.push_back({(i64)p2, 1});
                        }
                    }
                } else { continue; }
            }

            vector<i128> roots = {0}; i128 mod = 1; bool ok = true;
            for (auto [p, e] : small_facs[i]) {
                if (p <= 1) { ok = false; break; }
                i64 q = 1; for (int k = 0; k < e; ++k) q *= p;
                vector<i64> rq = (e == 1) ? small_root_cache[p] : lift_roots(114, p, e, small_root_cache[p]);
                if (rq.empty()) { ok = false; break; }
                roots = crt_combine128(roots, mod, rq, q); mod *= q;
            }
            if (!ok) continue;

            for (auto [p, e] : large_facs) {
                if (p <= 1) { ok = false; break; }
                i64 q = 1; for (int k = 0; k < e; ++k) q *= p;
                vector<i64> rp = cube_roots_mod_prime(114 % p, p);
                if (rp.empty()) { ok = false; break; }
                vector<i64> rq = (e == 1) ? rp : lift_roots(114, p, e, rp);
                roots = crt_combine128(roots, mod, rq, q); mod *= q;
            }
            if (!ok || roots.empty()) continue;

            chunk_valid_u++;

            for (i128 r : roots) {
                u64 k0 = (u64)(r % 3) + 1;

                if (!lattice_logged_this_chunk && k0 == 3) {
                    i128 y_sym = (i128)3 * u + r;
                    lattice_logged_this_chunk = true;
                    mat_ZZ B; B.SetDims(2, 2);
                    B[0][0] = to_ZZ((unsigned long)(u & 0xFFFFFFFFFFFFFFFFULL)); B[0][1] = ZZ(0);
                    B[1][0] = to_ZZ((unsigned long)(r & 0xFFFFFFFFFFFFFFFFULL)); B[1][1] = ZZ(1);
                    ZZ det2; LLL(det2, B, 99, 100);
                    stringstream b0s, b1s, ds;
                    b0s << "[" << B[0][0] << ", " << B[0][1] << "]"; b1s << "[" << B[1][0] << ", " << B[1][1] << "]"; ds << det2;
                    AngleMetrics am = calc_angle_metrics(u, y_sym);
                    redisReply* rl = (redisReply*)redisCommand(
                        c, "HMSET %s:lat:%d u %s r %s y %s b0 %s b1 %s det %s phi %.4f psi %.4f tan2 %.4f lam %.6f",
                        stream.c_str(), pid, format_i128(u).c_str(), format_i128(r).c_str(), format_i128(y_sym).c_str(),
                        b0s.str().c_str(), b1s.str().c_str(), ds.str().c_str(), am.phi_deg, am.psi_deg, am.tan2_phi, am.lambda_val
                    );
                    if (rl) freeReplyObject(rl);
                }

                for (u64 m = 0; m < k_steps; ++m) {
                    u64 k = k0 + 3 * m; i128 y = (i128)k * u + r;
                    chunk_y_checked++;

                    bool pass = true;
                    #pragma clang loop unroll(full)
                    for (int pi = 0; pi < 16; ++pi) {
                        if (!is_qr_fast(y, u, P_LIST[pi])) { pass = false; break; }
                    }
                    if (!pass) continue;
                    chunk_euler_surv++;

                    mpz_class my = to_mpz(y), mu = to_mpz(u);
                    mpz_class A = 4 * (((my * my * my) - 114) / mu) - (mu * mu * mu);
                    if (A > 0 && A % 3 == 0) {
                        mpz_class S2 = A / 3, s, rem;
                        mpz_sqrtrem(s.get_mpz_t(), rem.get_mpz_t(), S2.get_mpz_t());

                        AngleMetrics am = calc_angle_metrics(u, y);
                        string rem_s = rem.get_str().substr(0, 22) + "...";
                        redisReply* re = (redisReply*)redisCommand(
                            c, "HMSET %s:elite:latest u %s y %s phi %.4f psi %.4f lam %.6f rem %s",
                            stream.c_str(), format_i128(u).c_str(), format_i128(y).c_str(),
                            am.phi_deg, am.psi_deg, am.lambda_val, rem_s.c_str()
                        );
                        if (re) freeReplyObject(re);

                        if (rem == 0 && s > mu && (s - mu) % 2 == 0) {
                            mpz_class x = (s - mu) / 2, z = (s + mu) / 2;
                            if (x > 0 && x % 3 == 2 && my % 3 == 2 && z % 3 == 1) {
                                string sol = "FOUND! X=" + x.get_str() + ", Y=" + my.get_str() + ", Z=-" + z.get_str() + " (u=" + format_i128(u) + ")";
                                redisReply* r_sol = (redisReply*)redisCommand(c, "RPUSH %s:solutions %s", stream.c_str(), sol.c_str());
                                if (r_sol) freeReplyObject(r_sol);
                            }
                        }
                    }
                }
            }
        }

        redisReply* r1 = (redisReply*)redisCommand(c, "INCRBY %s:stat_u %llu", stream.c_str(), (unsigned long long)chunk_u_scanned); if (r1) freeReplyObject(r1);
        redisReply* r2 = (redisReply*)redisCommand(c, "INCRBY %s:stat_valid_u %llu", stream.c_str(), (unsigned long long)chunk_valid_u); if (r2) freeReplyObject(r2);
        redisReply* r3 = (redisReply*)redisCommand(c, "INCRBY %s:stat_y %llu", stream.c_str(), (unsigned long long)chunk_y_checked); if (r3) freeReplyObject(r3);
        redisReply* r4 = (redisReply*)redisCommand(c, "INCRBY %s:stat_euler %llu", stream.c_str(), (unsigned long long)chunk_euler_surv); if (r4) freeReplyObject(r4);
        redisReply* r5 = (redisReply*)redisCommand(c, "SET %s:curr_u %s", stream.c_str(), format_i128(u_end).c_str()); if (r5) freeReplyObject(r5);
    }
    redisFree(c);
    return 0;
}
