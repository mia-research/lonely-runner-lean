#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <string_view>
#include <utility>
#include <vector>

using I = std::int64_t;
constexpr I scale = I{1} << 25;
constexpr int slowCount = 5;
using Faces = std::array<I, slowCount>;

struct Rat {
    I n;
    I d;
};

bool operator<(Rat a, Rat b) { return a.n * b.d < b.n * a.d; }
bool operator<=(Rat a, Rat b) { return !(b < a); }
struct Interval { Rat lo, hi; };
using List = std::vector<Interval>;
struct Box { Faces lo, hi; };
struct Band { I low, high; };

bool normalize(Box& box) {
    for (int i = 1; i < slowCount; ++i)
        box.lo[i] = std::max(box.lo[i], box.lo[i-1]);
    for (int i = slowCount-2; i >= 0; --i)
        box.hi[i] = std::min(box.hi[i], box.hi[i+1]);
    for (int i = 0; i < slowCount; ++i)
        if (box.lo[i] > box.hi[i]) return false;
    return true;
}

// Time endpoints are stored in units of R/scale. All products fit int64.
List slowCells(const Box& box) {
    List cells{{{1,scale},{7,scale}},{{9,scale},{15,scale}}}, next;
    for (int i = 0; i < slowCount; ++i) {
        next.clear();
        for (auto cell : cells) {
            I start = std::max<I>(0, (cell.lo.n * box.hi[i] / cell.lo.d - 7) / 8);
            I stop = (cell.hi.n * box.lo[i] / cell.hi.d - 1) / 8;
            for (I j = start; j <= stop; ++j) {
                Rat lo = std::max(cell.lo, Rat{8*j+1,box.lo[i]});
                Rat hi = std::min(cell.hi, Rat{8*j+7,box.hi[i]});
                if (lo <= hi) next.push_back({lo,hi});
            }
        }
        cells.swap(next);
        if (cells.empty()) break;
    }
    return cells;
}

// Blocking intervals are open and use units of scale * x.
List blockers(Interval cell, I minX, I maxX) {
    List result;
    I start = std::max<I>(1, (minX * cell.lo.n / cell.lo.d - 1) / 8);
    I stop = (maxX * cell.hi.n / cell.hi.d + 1) / 8;
    for (I j = start; j <= stop; ++j) {
        Rat lo{(8*j-1)*cell.lo.d,cell.lo.n};
        Rat hi{(8*j+1)*cell.hi.d,cell.hi.n};
        if (lo < hi && lo < Rat{maxX,1} && Rat{minX,1} < hi)
            result.push_back({lo,hi});
    }
    return result;
}

bool disjoint(const List& first, const List& second, I minX, I maxX) {
    for (auto a : first)
        for (auto b : second) {
            Rat lo = std::max(a.lo,b.lo), hi = std::min(a.hi,b.hi);
            if (lo < hi && lo < Rat{maxX,1} && Rat{minX,1} < hi) return false;
        }
    return true;
}

struct Certificate {
    int size = 0;
    Interval first{}, second{};
};

Certificate certify(const Box& box, Band band) {
    const I minX = std::max(band.low,box.lo.back());
    std::vector<std::pair<Interval,List>> previous;
    for (auto cell : slowCells(box)) {
        auto bad = blockers(cell,minX,band.high);
        if (bad.empty()) return {1,cell,{}};
        for (const auto& earlier : previous)
            if (disjoint(earlier.second,bad,minX,band.high)) return {2,earlier.first,cell};
        previous.emplace_back(cell,std::move(bad));
    }
    return {};
}

struct Stats {
    I roots = 0, nodes = 0, singles = 0, pairs = 0, unresolved = 0;
    int maxDepth = 0;
    bool emit = false;
};

void printBox(const Box& box) {
    std::cout << "box";
    for (int i=0; i<slowCount; ++i) std::cout << ' ' << box.lo[i] << ':' << box.hi[i];
}

void check(Box box, int depth, int cap, Band band, Stats& stats) {
    if (!normalize(box)) {
        if (stats.emit) std::cout << "E\n";
        return;
    }
    ++stats.nodes;
    stats.maxDepth = std::max(stats.maxDepth, depth);
    const auto proof = certify(box,band);
    if (proof.size) {
        if (proof.size == 1) ++stats.singles;
        else ++stats.pairs;
        if (stats.emit) {
            const auto write = [](Interval gap) {
                std::cout << ' ' << gap.lo.n << ' ' << gap.lo.d
                          << ' ' << gap.hi.n << ' ' << gap.hi.d;
            };
            std::cout << proof.size;
            write(proof.first);
            if (proof.size == 2) write(proof.second);
            std::cout << '\n';
        }
        return;
    }
    if (depth == cap) {
        ++stats.unresolved;
        if (stats.emit) std::cout << "U\n";
        if (!stats.emit && stats.unresolved <= 16) {
            printBox(box);
            std::cout << " unresolved\n" << std::flush;
        }
        return;
    }
    int widest = 0;
    for (int i=1; i<slowCount; ++i) {
        if ((box.hi[i]-box.lo[i])*box.lo[widest] >
            (box.hi[widest]-box.lo[widest])*box.lo[i])
            widest = i;
    }
    I mid = (box.lo[widest]+box.hi[widest])/2;
    if (!(box.lo[widest] < mid && mid < box.hi[widest]))
        throw std::logic_error("dyadic grid exhausted");
    if (stats.emit) std::cout << "S " << widest << '\n';
    Box right = box;
    box.hi[widest] = mid;
    right.lo[widest] = mid;
    check(box,depth+1,cap,band,stats);
    check(right,depth+1,cap,band,stats);
}

void roots(int i, int n, Box box, int first, int last, int cap, Band band, Stats& stats) {
    if (i == slowCount) {
        ++stats.roots;
        check(box,0,cap,band,stats);
        return;
    }
    for (int k = n; k <= (i == 0 ? last : 25); ++k) {
        if (i == 0 && k < first) continue;
        box.lo[i] = std::max(scale, (2*k-1)*scale/2);
        box.hi[i] = std::min(band.high, (2*k+1)*scale/2);
        roots(i+1,k,box,first,last,cap,band,stats);
    }
}

int main(int argc, char** argv) {
    int first = argc > 1 ? std::atoi(argv[1]) : 1;
    int last = argc > 2 ? std::atoi(argv[2]) : 25;
    int cap = argc > 3 ? std::atoi(argv[3]) : 22;
    std::ios::sync_with_stdio(false);
    Stats stats;
    Band band{23*scale,25*scale};
    for (int i=4;i<argc;++i) {
        const std::string_view flag = argv[i];
        if (flag=="--certificate") stats.emit = true;
        else if (flag=="--wide") band = {45*scale/2,51*scale/2};
        else throw std::invalid_argument("unknown flag");
    }
    if (stats.emit)
        std::cout << "X24PAIR 1 " << scale << ' ' << first << ' ' << last << ' '
                  << band.low << ' ' << band.high << '\n';
    roots(0,1,{},first,last,cap,band,stats);
    auto& log = stats.emit ? std::cerr : std::cout;
    log << "scale " << scale << " top " << band.low << ":" << band.high << " roots " << stats.roots << " nodes " << stats.nodes
              << " singles " << stats.singles << " pairs " << stats.pairs
              << " unresolved " << stats.unresolved << " depth " << stats.maxDepth << '\n';
}
