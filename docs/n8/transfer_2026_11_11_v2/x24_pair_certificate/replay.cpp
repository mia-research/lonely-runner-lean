// Independent checker for a streamed one-/two-gap proof of the entire X24 band.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using I = std::int64_t;
using Wide = __int128_t;
constexpr I D = I{1} << 25;
using Bounds = std::array<I,5>;
struct Box { Bounds low, high; };
struct Band { I low, high; };
struct Rational { I num, den; };
struct Interval { Rational low, high; };

bool less(Rational a, Rational b) {
    return Wide(a.num)*b.den < Wide(b.num)*a.den;
}

void require(bool condition, const char* message) {
    if (!condition) throw std::runtime_error(message);
}

Interval readGap(I maximum) {
    Interval gap;
    require(bool(std::cin >> gap.low.num >> gap.low.den >> gap.high.num >> gap.high.den),
            "missing gap endpoints");
    for (auto p : {gap.low,gap.high})
        require(p.num>0 && p.num<=383 && p.den>0 && p.den<=maximum, "invalid gap endpoint");
    require(!less(gap.high,gap.low), "empty slow gap");
    return gap;
}

// Verify the whole product interval of a time cell and a reading face.
void checkPhase(Interval gap, I low, I high) {
    const I product = gap.low.num*low;
    require(product >= gap.low.den, "phase below its first clear gap");
    const I lap = (product-gap.low.den)/(8*gap.low.den);
    require(gap.high.num*high <= (8*lap+7)*gap.high.den, "slow face crosses a bad phase");
}

void verifySlow(Interval gap, const Box& box) {
    const auto contains = [&](I low, I high) {
        return !less(gap.low,{low,D}) && !less({high,D},gap.high);
    };
    require(contains(1,7)||contains(9,15), "gap outside the two windows");
    for (int i=0; i<5; ++i) checkPhase(gap,box.low[i],box.high[i]);
}

// These are open intervals in D*x. Keep them unclipped to preserve
// membership at both closed ends of the admissible reading range.
std::vector<Interval> badIntervals(Interval gap, I minimum, I maximum) {
    std::vector<Interval> result;
    for (I j=1; j<=47; ++j) {
        const Rational left{(8*j-1)*gap.low.den,gap.low.num};
        const Rational right{(8*j+1)*gap.high.den,gap.high.num};
        if (less(left,right) && less(left,{maximum,1}) && less({minimum,1},right))
            result.push_back({left,right});
    }
    return result;
}

struct Counts { I roots=0, split=0, empty=0, one=0, two=0; int depth=0; };

void checkTree(Box box, Band band, Counts& counts, int depth) {
    counts.depth=std::max(counts.depth,depth);
    require(depth<=128,"excessive split depth");
    char tag;
    require(bool(std::cin >> tag),"truncated certificate");
    for (int i=1;i<5;++i)
        if (box.low[i-1]>box.low[i]) box.low[i]=box.low[i-1];
    for (int i=4;i>0;--i)
        if (box.high[i-1]>box.high[i]) box.high[i-1]=box.high[i];
    for (int i=0;i<5;++i) if (box.low[i]>box.high[i]) {
        require(tag=='E',"empty box requires E");
        ++counts.empty;
        return;
    }
    if (tag=='S') {
        int axis;
        require(bool(std::cin >> axis) && axis>=0 && axis<5,"invalid split axis");
        const I mid=box.low[axis]+(box.high[axis]-box.low[axis])/2;
        require(box.low[axis]<mid && mid<box.high[axis],"invalid split point");
        Box upper=box;
        box.high[axis]=mid;
        upper.low[axis]=mid;
        ++counts.split;
        checkTree(box,band,counts,depth+1);
        checkTree(upper,band,counts,depth+1);
        return;
    }
    require(tag=='1'||tag=='2',"nonempty leaf has no proof");
    const I minimum=std::max(band.low,box.low.back());
    const auto first=readGap(band.high);
    verifySlow(first,box);
    const auto badFirst=badIntervals(first,minimum,band.high);
    if (tag=='1') {
        require(badFirst.empty(),"single cell can be blocked");
        ++counts.one;
        return;
    }
    const auto second=readGap(band.high);
    verifySlow(second,box);
    const auto badSecond=badIntervals(second,minimum,band.high);
    for (auto a : badFirst) for (auto b : badSecond) {
        // The intervals already intersect the admissible domain, so
        // cross-testing both endpoints detects any simultaneous blocker.
        require(!less(a.low,b.high)||!less(b.low,a.high),"both cells can be blocked");
    }
    ++counts.two;
}

int main() {
    std::ios::sync_with_stdio(false);
    try {
        std::string header;
        int version, first, last;
        I scale;
        Band band;
        require(bool(std::cin >> header >> version >> scale >> first >> last >> band.low >> band.high)
                && header=="X24PAIR" && version==1 && scale==D && first==1 && last==25,
                "expected certificate for the full X24 domain");
        require((band.low==23*D && band.high==25*D) ||
                (band.low==45*D/2 && band.high==51*D/2), "unsupported top band");
        Counts counts;
        for (int a=1;a<=25;++a) for (int b=a;b<=25;++b)
            for (int c=b;c<=25;++c) for (int d=c;d<=25;++d) for (int e=d;e<=25;++e) {
                const std::array<int,5> index{a,b,c,d,e};
                Box box;
                for (int i=0;i<5;++i) {
                    box.low[i]=std::max(D,index[i]*D-D/2);
                    box.high[i]=std::min(band.high,index[i]*D+D/2);
                }
                ++counts.roots;
                checkTree(box,band,counts,0);
            }
        char extra;
        require(!(std::cin>>extra),"trailing certificate data");
        std::cout << "verified top " << band.low << ":" << band.high << " roots " << counts.roots << " splits " << counts.split
                  << " empty " << counts.empty << " single leaves " << counts.one
                  << " pair leaves " << counts.two << " max depth " << counts.depth << '\n';
    } catch (const std::exception& error) {
        std::cerr << "invalid certificate: " << error.what() << '\n';
        return 1;
    }
}
