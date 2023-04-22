// compile flags: -std=c++17 -O2 -DLOCAL

/*
This file contains code for the paper "Minimum-Entropy Coupling Approximation Guarantees Beyond the Majorization Barrier."

See the main method for functions of potential interest.

For another implementation of the polynomial-time greedy coupling algorithm, this can already be found elsewhere, such as at
https://github.com/schroederdewitt/perfectly-secure-steganography/blob/178625910599bf1fe9a0b3841ad02f27b5fe7111/src/mec.py

*/
#include <algorithm>
#include <array>
#include <bitset>
#include <cassert>
#include <chrono>
#include <climits>
#include <cmath>
#include <complex>
#include <cstring>
#include <functional>
#include <iomanip>
#include <iostream>
#include <map>
#include <numeric>
#include <queue>
#include <random>
#include <set>
#include <vector>
#include <fstream>
using namespace std;

#include "macros.h"


namespace Common {

using P = V<db>; // probability distribution

const db EPS = 1e-12;
bool close(db a, db b) { return abs(a - b) < EPS; }
db H(db t) {
	assert(t >= -EPS);
	return t <= 0 ? 0 : t * log2(1 / t);
}
db H(const P &p) {
	db ans = 0;
	each(t, p) ans += H(t);
	return ans;
}

void check_full(const P &p) {
	db ans = 0;
	each(t, p) ans += t;
	assert(close(ans, 1));
}

db sum(const P &p) {
	db ans = 0;
	each(t, p) ans += t;
	return ans;
}

db get_equal_sum(const V<P> &v) {
	assert(sz(v));
	auto s = sum(v[0]);
	FOR(i, 1, sz(v)) assert(close(sum(v[i]), s));
	return s;
}

} // namespace Common

using namespace Common;

namespace Greed {

db calc_none(V<P> v){
	return 0.0;
}

db calc_and(V<P> v) {
	get_equal_sum(v);
	int M = 0;
	each(t, v) {
		sort(rall(t));
		ckmax(M, sz(t));
	}
	P psum(sz(v));
	db cur_sum = 0, res = 0;
	F0R(j, M) {
		db min_sum = 1;
		F0R(i, sz(v)) if (j < sz(v[i])) {
			psum.at(i) += v[i].at(j);
			ckmin(min_sum, psum.at(i));
		}
		res += H(min_sum - cur_sum);
		cur_sum = min_sum;
	}
	return res;
}

db calc_profile(V<P> v) {
	const db sum = get_equal_sum(v);
	V<pair<db, db>> vert;
	vert.pb({0, 0});
	each(t, v) {
		sor(t);
		db cum = 0;
		F0R(i, sz(t)) {
			cum += t[i];
			vert.pb({cum, t[i]});
		}
	}
	sort(rall(vert));
	db cur = 1, lst = sum, ans = 0;
	for (auto [x, y] : vert) {
		if (cur == 0) break;
		ans += (lst - x) * log2(1 / cur);
		lst = x;
		ckmin(cur, y);
	}
	return ans;
}

db calc_greed(const V<P> &v) {
	V<priority_queue<db>> best;
	F0R(i, sz(v)) {
		check_full(v[i]);
		best.eb();
		each(u, v[i]) best.bk.push(u);
	}
	db ans = 0;
	while (true) {
		db mn = 1;
		each(t, best) {
			if (!sz(t)) goto done;
			ckmin(mn, t.top());
		}
		ans += H(mn);
		each(t, best) {
			auto u = t.top();
			t.pop();
			u -= mn;
			if (u > 0) t.push(u);
		}
	}
done:
	return ans;
}


db calc_profile_cap(V<P> v) {
	const db sum = get_equal_sum(v);
	V<pair<db, db>> vert;
	vert.pb({0, 0});
	each(t, v) {
		sor(t);
		db cum = 0;
		F0R(i, sz(t)) {
			cum += t[i];
			vert.pb({cum, t[i]});
		}
	}
	{
		sort(rall(vert));
		V<pair<db, db>> nvert;
		db min_so_far = 2;
		each(t, vert) if (ckmin(min_so_far, t.s)) nvert.pb(t);
		swap(vert, nvert);
	}
	auto pair_sum = [&](pair<db, db> p) { return p.f + p.s; };
	db cur = sum, ans = 0, min_y = 1.0;
	for (int i_vert = 0; cur > 0;) {
		for (; pair_sum(vert.at(i_vert)) > cur; ++i_vert) {
			ckmin(min_y, vert.at(i_vert).s);
		}
		db state = min(min_y, cur - vert.at(i_vert).f);
		cur -= state;
		ans += H(state);
	}
	return ans;
}

} // namespace Greed

namespace Enumerate {

db best;
int visited = 0;

db dfs_slow(P &p, int used, int killed, db ans_so_far, db prob_so_far, int n1) {
	if (__builtin_popcount(killed) == sz(p) - 1) {
		++visited;
		each(t, p) if (t < -EPS) return BIG;
		assert(prob_so_far > 1 - EPS);
		return ans_so_far;
	}
	db ret = BIG;
	FOR(i, 1, sz(p)) if (!(killed & (1 << i))) if (!(used & (1 << i))) {
		const db cur_p = max(p.at(i), 0.0);
		F0R(j, sz(p))
		if ((j < n1) != (i < n1))
			if (!(killed & (1 << j))) {
				p.at(j) -= cur_p;
				ckmin(ret,
					  dfs_slow(p, used ^ (used & (1 << j)), killed ^ (1 << i),
							   ans_so_far + H(cur_p), prob_so_far + cur_p, n1));
				p.at(j) += cur_p;
			}
		used ^= 1 << i;
	}
	return ret;
}

db solve_slow(const V<P> &x) {
	visited = 0;
	P new_x;
	each(t, x.at(0)) new_x.pb(t);
	each(t, x.at(1)) new_x.pb(t);
	return dfs_slow(new_x, 0, 0, 0, 0, sz(x.at(0)));
}

void dfs(P &p, int used, db ans_so_far, db prob_so_far) {
	++visited;
	if (ans_so_far >= best) return;
	if (prob_so_far > 1 - EPS) {
		best = ans_so_far;
		return;
	}
	FOR(i, 1, sz(p)) if (!(used & (1 << i)) && p.at(i) > 0) {
		const db cur_p = p.at(i);
		F0R(j, sz(p))
		if (j / (sz(p) / 2) != i / (sz(p) / 2))
			if (p.at(i) <= p.at(j) + EPS) {
				p.at(j) -= cur_p, p.at(i) -= cur_p;
				dfs(p, used ^ (used & (1 << j)), ans_so_far + H(cur_p),
					prob_so_far + cur_p);
				p.at(j) += cur_p, p.at(i) += cur_p;
			}
		used ^= 1 << i;
	}
}

db solve(const V<P> &x) {
	visited = 0;
	best = BIG;
	P res;
	each(t, x.at(0)) res.pb(t);
	each(t, x.at(1)) res.pb(t);
	dfs(res, 0, 0, 0);
	return best;
}

} // namespace Enumerate

namespace Backtrack {

using namespace Greed;

struct Prob {
	db prob;
	int side;
	bool used;
	int id;
	pair<db, int> get_pair() const { return mp(prob, id); }
	bool operator<(const Prob &o) const { return get_pair() < o.get_pair(); }
};

db calc_none([[maybe_unused]] const V<Prob> &v) { return 0; }

db calc_and(const V<Prob> &v) {
	V<P> w(2);
	each(t, v) w.at(t.side).pb(t.prob);
	return Greed::calc_and(w);
}

db calc_profile(const V<Prob> &v) {
	V<P> w(2);
	each(t, v) w.at(t.side).pb(t.prob);
	return Greed::calc_profile(w);
}

db calc_profile_cap(const V<Prob> &v) {
	V<P> w(2);
	each(t, v) w.at(t.side).pb(t.prob);
	return Greed::calc_profile_cap(w);
}

db best;
template <class F>
void dfs_backtrack(const F &f, V<Prob> x, db cur_ans, db cur_prob) {
	db cap = f(x);
	if (cur_ans + cap >= best) return;
	if (cur_prob > 1 - EPS) {
		best = cur_ans;
		return;
	}
	sort(rall(x));
	F0R(i, sz(x)) if (!x[i].used) {
		const double p = x[i].prob;
		F0R(j, i) if (x[i].side != x[j].side) {
			db next_ans = cur_ans + H(p);
			auto y = x;
			y.erase(begin(y) + i);
			y[j].prob -= p;
			y[j].used = 0;
			dfs_backtrack(f, y, next_ans, cur_prob + p);
		}
		x[i].used = 1;
	}
}

template <class F>
void dfs_monotone(const F &f, V<P> x, db cur_ans, db cur_prob, db last_prob) {
	db cap = f(x);
	each(t, x) {
		sort(rall(t));
		while (sz(t) && t.bk <= 0) t.pop_back();
	}
	if (cur_ans + cap >= best) return;
	if (cur_prob > 1 - EPS) {
		best = cur_ans;
		return;
	}
	F0R(i, sz(x[0])) F0R(j, sz(x[1])) {
		db mn = min(x[0][i], x[1][j]);
		if (mn <= last_prob) {
			x[0][i] -= mn, x[1][j] -= mn;
			dfs_monotone(f, x, cur_ans + H(mn), cur_prob + mn, mn);
			x[0][i] += mn, x[1][j] += mn;
		}
	}
}

db solve_monotone(const function<db(const V<P> &)> &f, V<P> x) {
	best = BIG;
	each(t, x) sort(rall(t));
	dfs_monotone(f, x, 0, 0, BIG);
	return best;
}

db solve(const function<db(const V<Prob> &)> &f, const V<P> &x) {
	best = BIG;
	V<Prob> v;
	int id = 0;
	F0R(i, 2) each(p, x[i]) v.pb({p, i, 0, id++});
	dfs_backtrack(f, v, 0, 0);
	return best;
}

db solve_none(const V<P> &x) { return solve(calc_none, x); }
db solve_and(const V<P> &x) { return solve(calc_and, x); }
db solve_profile(const V<P> &x) { return solve(calc_profile, x); }
db solve_profile_cap(const V<P> &x) { return solve(calc_profile_cap, x); }


db solve_none_monotone(const V<P> &x) { return solve_monotone(Greed::calc_none, x); }
db solve_and_monotone(const V<P> &x) { return solve_monotone(Greed::calc_and, x); }
db solve_profile_monotone(const V<P> &x) { return solve_monotone(Greed::calc_profile, x); }
db solve_profile_cap_monotone(const V<P> &x) { return solve_monotone(Greed::calc_profile_cap, x); }

} // namespace Backtrack

namespace Bitmask {

db solve(V<P> x) {
	assert(sz(x) == 2);
	const int TOT = sz(x.at(0)) + sz(x.at(1));
	V<V<db>> dp(1 << TOT, V<db>(TOT, BIG));
	V<V<db>> dif(1 << TOT, V<db>(TOT));
	auto side = [&](int p) { return p < sz(x[0]); };
	auto val = [&](int p) {
		if (p < sz(x[0])) return x[0].at(p);
		return x[1].at(p - sz(x[0]));
	};
	F0R(j, TOT) dp.at(1 << j).at(j) = 0;
	F0R(mask, 1 << TOT) F0R(j, TOT) if (mask & (1 << j)) {
		if (mask & 1) {
			if (j != 0) continue;
		}
		F0R(k, TOT) if (mask & (1 << k)) {
			if (side(j) == side(k)) dif.at(mask).at(j) += val(k);
			else dif.at(mask).at(j) -= val(k);
		}
		if (dif.at(mask).at(j) >= -EPS) {
			const int mask_wo = mask ^ (1 << j);
			{ // augment
				F0R(k, TOT) {
					if (mask_wo & (1 << k))
						if (side(j) != side(k))
							if (dif.at(mask_wo).at(k) >= -EPS) {
								ckmin(dp.at(mask).at(j),
									  dp.at(mask_wo).at(k) +
										  H(dif.at(mask_wo).at(k)));
							}
				}
			}
			if (mask_wo) {
				for (int k = (mask_wo - 1) & mask_wo;; k = (k - 1) & mask_wo) {
					if (2 * k < mask_wo) break;
					ckmin(dp.at(mask).at(j),
						  dp.at((1 << j) ^ k).at(j) +
							  dp.at((1 << j) ^ k ^ mask_wo).at(j));
				}
			}
		}
	}
	return dp.at(sz(dp) - 1).at(0);
}

} // namespace Bitmask


int main() {

	// Example distributions
	vector<double> p = {0.5, 0.4, 0.1};
	vector<double> q = {0.6, 0.2, 0.2};
	vector<vector<double> > combined = {p, q};
	
	// -----------------------------------

	// ** Lower Bounds **

	// Majorization Lower Bound
	cout << "Majorization Lower Bound: " << Greed::calc_and(combined) << endl;
	// Profile Lower Bound
	cout << "Profile Lower Bound: " << Greed::calc_profile(combined) << endl;
	// Majorize-Profile Lower Bound [this is provably always the best among the three lower bounds]
	cout << "Majorize-Profile Lower Bound: " << Greed::calc_profile_cap(combined) << endl;

	// -----------------------------------

	// ** Greedy Coupling (Approximation) **
	
	cout << "Greedy Coupling (Approximation): " << Greed::calc_greed(combined) << endl;

	// -----------------------------------
	
	// ** Exponential-Time Coupling (Exact) **

	// Naive Polytope Vertex Enumeration
	cout << "Naive Polytope Vertex Enumeration (Exact): " << Enumerate::solve_slow(combined) << endl;
	// Backtracking using 0 as the lower bound
	cout << "Backtracking [0] (Exact): " << Backtrack::solve_none_monotone(combined) << endl;
	// Backtracking using majorization lower bound
	cout << "Backtracking [Majorization] (Exact): " << Backtrack::solve_and_monotone(combined) << endl;
	// Backtracking using profile lower bound
	cout << "Backtracking [Profile] (Exact): " << Backtrack::solve_profile_monotone(combined) << endl;
	// Backtracking using Majorize-Profile Lower Bound
	cout << "Backtracking [Majorize-Profile] (Exact): " << Backtrack::solve_profile_cap_monotone(combined) << endl;
	// Dynamic Programming
	cout << "Dynamic Programming (Exact): " << Bitmask::solve(combined) << endl;
	
	// -----------------------------------
}