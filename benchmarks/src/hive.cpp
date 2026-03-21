#include <array>
#include <benchmark/benchmark.h>
#include <deque>
#include <format>
#include <hive>
#include <memory_resource>
#include <random>
#include <ranges>

#include "skewed_allocator.hpp"

using namespace std;

template <class Hive>
void rnd_erase(Hive& cont) {
    using hive_t = Hive;
    using iter_t = hive_t::iterator;

    vector<iter_t> iters(cont.size());
    auto it = cont.begin();
    for (auto& iter : iters) {
        iter = it;
        ++it;
    }
    ranges::shuffle(iters, mt19937_64(42));

    const size_t erase_count = cont.size() / 2;
    for (size_t i = 0; i != erase_count; ++i) {
        cont.erase(iters[i]);
    }
}

template <class T, class Alloc>
void rnd(size_t cnt, hive<T, Alloc>& target) {
    target.insert(cnt * 2, T{});
    rnd_erase(target);
}
template <class T, class Alloc>
void full(size_t cnt, hive<T, Alloc>& target) {
    target.insert(cnt, T{});
}

size_t get_count(benchmark::State& state) {
    return static_cast<size_t>(state.range(0));
}
hive_limits get_limits(benchmark::State& state) {
    return {static_cast<size_t>(state.range(1)), static_cast<size_t>(state.range(2))};
}

template <class T, class Alloc>
struct unsized_rng : private vector<T, Alloc> {
    static_assert(!is_same_v<T, bool>);

    using value_type      = T;
    using allocator_type  = Alloc;
    using pointer         = T*;
    using const_pointer   = const T*;
    using reference       = T&;
    using const_reference = const T&;
    using size_type       = size_t;
    using difference_type = ptrdiff_t;

    struct iter {
        using iterator_concept  = forward_iterator_tag;
        using iterator_category = forward_iterator_tag;
        using value_type        = T;
        using difference_type   = ptrdiff_t;
        using pointer           = const T*;
        using reference         = const T&;

        reference operator*() const noexcept {
            return *ptr;
        }
        pointer operator->() const noexcept {
            return ptr;
        }

        inline static volatile size_t one = 1; // avoid auto-vectorization
        iter& operator++() noexcept {
            ptr += one;
            return *this;
        }
        iter operator++(int) noexcept {
            const auto tmp = *this;
            ptr += one;
            return tmp;
        }

        bool operator==(const iter&) const = default;

        pointer ptr;
    };

    using iterator       = iter;
    using const_iterator = iter;

    using vector<T, Alloc>::vector;

    const_iterator begin() const noexcept {
        return {this->data()};
    }
    const_iterator end() const noexcept {
        return {this->data() + this->size()};
    }
};

template <class T, template <class> class Alloc>
struct ctor {
    using hive_t  = hive<T, Alloc<T>>;
    using maker_t = void (*)(size_t, hive_t&);

    static void d_fill(benchmark::State& state) {
        const auto cnt    = get_count(state);
        const auto limits = get_limits(state);
        for (auto _ : state) {
            hive_t cont(cnt, limits);
            benchmark::DoNotOptimize(cont);
        }
    }

    static void fil(benchmark::State& state) {
        const auto cnt    = get_count(state);
        const auto limits = get_limits(state);
        for (auto _ : state) {
            hive_t cont(cnt, T{1}, limits);
            benchmark::DoNotOptimize(cont);
        }
    }

    template <template <class, class> class SeqCont>
    static void rng(benchmark::State& state) {
        const auto limits = get_limits(state);
        const auto src    = SeqCont<T, Alloc<T>>(get_count(state), T{1});
        for (auto _ : state) {
            hive_t cont(from_range, src, limits);
            benchmark::DoNotOptimize(cont);
        }
    }

    template <maker_t maker>
    static void cpy(benchmark::State& state) {
        const auto cnt    = get_count(state);
        const auto limits = get_limits(state);
        hive_t src(limits);
        maker(cnt, src);
        for (auto _ : state) {
            hive_t cont = src;
            benchmark::DoNotOptimize(cont);
        }
    }
};

template <class T, template <class> class Alloc>
struct ins_rnd {
    using hive_t = hive<T, Alloc<T>>;

    static void fil(benchmark::State& state) {
        const auto cnt    = get_count(state);
        const auto limits = get_limits(state);
        for (auto _ : state) {
            hive_t cont(cnt * 2, limits);
            rnd_erase(cont);
            cont.insert(cnt, T{1});
            benchmark::DoNotOptimize(cont);
        }
    }

    static void single(benchmark::State& state) {
        const auto cnt    = get_count(state);
        const auto limits = get_limits(state);
        for (auto _ : state) {
            hive_t cont(cnt * 2, limits);
            rnd_erase(cont);
            for (auto i = 0uz; i != cnt; ++i) {
                cont.insert(T{1});
            }
            benchmark::DoNotOptimize(cont);
        }
    }

    template <template <class, class> class SeqCont>
    static void rng(benchmark::State& state) {
        const auto cnt    = get_count(state);
        const auto limits = get_limits(state);
        const auto src    = SeqCont<T, Alloc<T>>(get_count(state), T{1});
        for (auto _ : state) {
            hive_t cont(cnt * 2, limits);
            rnd_erase(cont);
            cont.insert_range(src);
            benchmark::DoNotOptimize(cont);
        }
    }
};

template <class T, template <class> class Alloc>
struct del {
    using hive_t  = hive<T, Alloc<T>>;
    using maker_t = void (*)(size_t, hive_t&);

    static void single(benchmark::State& state) {
        const auto cnt    = get_count(state);
        const auto limits = get_limits(state);
        for (auto _ : state) {
            hive_t cont(cnt * 2, limits);
            rnd_erase(cont);
            benchmark::DoNotOptimize(cont);
        }
    }

    template <maker_t maker>
    static void rng(benchmark::State& state) {
        const auto cnt    = get_count(state);
        const auto limits = get_limits(state);
        for (auto _ : state) {
            hive_t cont(limits);
            maker(cnt * 2, cont);
            cont.erase(next(cont.begin(), cnt / 2), prev(cont.end(), cnt / 2));
            benchmark::DoNotOptimize(cont);
        }
    }
};

template <class T, template <class> class Alloc>
struct assign {
    using hive_t  = hive<T, Alloc<T>>;
    using maker_t = void (*)(size_t, hive_t&);

    template <maker_t maker>
    static void fil(benchmark::State& state) {
        const auto cnt    = get_count(state);
        const auto limits = get_limits(state);
        for (auto _ : state) {
            hive_t cont(limits);
            maker(cnt, cont);
            cont.assign(cnt, T{1});
            benchmark::DoNotOptimize(cont);
        }
    }

    template <template <class, class> class SeqCont, maker_t maker>
    static void rng(benchmark::State& state) {
        const auto cnt    = get_count(state);
        const auto limits = get_limits(state);
        const auto src    = SeqCont<T, Alloc<T>>(get_count(state), T{1});
        for (auto _ : state) {
            hive_t cont(limits);
            maker(cnt, cont);
            cont.assign_range(src);
            benchmark::DoNotOptimize(cont);
        }
    }

    template <maker_t maker>
    static void vec(benchmark::State& state) {
        rng<vector, maker>(state);
    }
    template <maker_t maker>
    static void deq(benchmark::State& state) {
        rng<deque, maker>(state);
    }
    template <maker_t maker>
    static void unsized(benchmark::State& state) {
        rng<unsized_rng, maker>(state);
    }

    template <maker_t src_maker, maker_t dst_maker>
    static void cpy(benchmark::State& state) {
        const auto cnt    = get_count(state);
        const auto limits = get_limits(state);
        hive_t src(limits);
        src_maker(cnt, src);
        for (auto _ : state) {
            hive_t dst(limits);
            dst_maker(cnt, dst);
            dst = src;
            benchmark::DoNotOptimize(dst);
        }
    }
    static void cpy_f2f(benchmark::State& state) {
        cpy<full, full>(state);
    }
    static void cpy_r2r(benchmark::State& state) {
        cpy<rnd, rnd>(state);
    }
};

template <class T, template <class> class Alloc>
struct iter {
    using hive_t  = hive<T, Alloc<T>>;
    using maker_t = void (*)(size_t, hive_t&);

    template <maker_t maker>
    static void fwd(benchmark::State& state) {
        const auto cnt    = get_count(state);
        const auto limits = get_limits(state);
        hive_t cont(limits);
        maker(cnt, cont);
        for (auto _ : state) {
            for (auto& val : cont) {
                benchmark::DoNotOptimize(val);
            }
        }
    }

    template <maker_t maker>
    static void foreach_(benchmark::State& state) {
        const auto cnt    = get_count(state);
        const auto limits = get_limits(state);
        hive_t cont(limits);
        maker(cnt, cont);
        for (auto _ : state) {
            ranges::for_each(cont, [](auto& val) static { benchmark::DoNotOptimize(val); });
        }
    }

    template <maker_t maker>
    static void adv(benchmark::State& state) {
        const auto cnt    = get_count(state);
        const auto limits = get_limits(state);
        hive_t cont(limits);
        maker(cnt, cont);
        for (auto _ : state) {
            auto it = cont.begin();
            advance(it, static_cast<hive_t::difference_type>(cont.size()));
            benchmark::DoNotOptimize(it);
        }
    }
};

template <class T, template <class> class Alloc>
struct misc {
    using hive_t = hive<T, Alloc<T>>;

    static constexpr void unique_single(benchmark::State& state) {
        const auto cnt    = get_count(state);
        const auto limits = get_limits(state);
        const auto src    = views::iota(0uz, cnt)
                       | views::transform([](size_t idx) { return static_cast<T>(idx % 4 / 2); })
                       | ranges::to<vector>(); // {0, 0, 1, 1, 0, 0, ...}
        for (auto _ : state) {
            hive_t cont(from_range, src, limits);
            cont.unique();
            benchmark::DoNotOptimize(cont);
        }
    }

    static constexpr void unique_rand(benchmark::State& state) {
        const auto cnt    = get_count(state);
        const auto limits = get_limits(state);
        vector<T> src;
        src.reserve(cnt);
        src.insert(src.end(), cnt / 2, T{0});
        src.insert(src.end(), cnt - cnt / 2, T{1});
        ranges::shuffle(src, mt19937_64{42});
        for (auto _ : state) {
            hive_t cont(from_range, src, limits);
            cont.unique();
            benchmark::DoNotOptimize(cont);
        }
    }

    static constexpr void erase_if_single(benchmark::State& state) {
        const auto cnt    = get_count(state);
        const auto limits = get_limits(state);
        for (auto _ : state) {
            hive_t cont(cnt, limits);
            bool flag = false;
            erase_if(cont, [&](const T&) { return flag = !flag; });
            benchmark::DoNotOptimize(cont);
        }
    }

    static constexpr void erase_if_rand(benchmark::State& state) {
        const auto cnt    = get_count(state);
        const auto limits = get_limits(state);
        vector<T> src;
        src.reserve(cnt);
        src.insert(src.end(), cnt / 2, T{0});
        src.insert(src.end(), cnt - cnt / 2, T{1});
        ranges::shuffle(src, mt19937_64{42});
        for (auto _ : state) {
            hive_t cont(cnt, limits);
            erase_if(cont, [&](const T& val) { return val == 0; });
            benchmark::DoNotOptimize(cont);
        }
    }
};

template <class T, template <class> class Alloc, class Ratio = ratio<1>>
void common_args(benchmark::Benchmark* bm) {
    const auto limits_arr = [] {
        if constexpr (false) {
            if constexpr (sizeof(T) <= 3) {
                return to_array<hive_limits>({{160, 160}, {200, 200}, {255, 255}});
            } else {
                return to_array<hive_limits>({{3600, 3600}, {4000, 4000}, {4400, 4400}});
            }
        } else {
            return array{hive<T, Alloc<T>>::block_capacity_default_limits()};
        }
    }();

    constexpr auto counts_arr = [] {
        if constexpr (sizeof(T) <= 3) {
            return array{64, 256, 2048, 65536, 524288, 2097152};
        } else {
            return array{2048, 8192, 32768, 131072, 524288, 2097152};
        }
    }();

    for (const auto& [limits_min, limits_max] : limits_arr) {
        for (const auto cnt : counts_arr) {
            bm->Args({static_cast<int64_t>(cnt * Ratio::num / Ratio::den), static_cast<int64_t>(limits_min),
                static_cast<int64_t>(limits_max)});
        }
    }
}

template <class T>
using stdal = allocator<T>;
template <class T>
using haal = highly_aligned_allocator<T>;
template <class T>
using nhaal = not_highly_aligned_allocator<T>;

using i8  = int8_t;
using i16 = int16_t;
using i64 = int64_t;

#define BENCHMARK_ONE(category, func, type, al, ...) \
    BENCHMARK(category<type, al>::func)->Apply(common_args<type, al __VA_OPT__(, ) __VA_ARGS__>)

#define BENCHMARK_MAT(category, func, al, ...)                         \
    BENCHMARK_ONE(category, func, i8, al __VA_OPT__(, ) __VA_ARGS__);  \
    BENCHMARK_ONE(category, func, i16, al __VA_OPT__(, ) __VA_ARGS__); \
    BENCHMARK_ONE(category, func, i64, al __VA_OPT__(, ) __VA_ARGS__)

template <class T, class Alloc>
using vec = vector<T, Alloc>;
template <class T, class Alloc>
using deq = deque<T, Alloc>;
template <class T, class Alloc>
using unsized = unsized_rng<T, Alloc>;

BENCHMARK_MAT(ctor, d_fill, haal);
BENCHMARK_MAT(ctor, fil, haal);
BENCHMARK_MAT(ctor, rng<vec>, haal);
BENCHMARK_MAT(ctor, rng<deq>, haal);
BENCHMARK_MAT(ctor, rng<unsized>, haal);
BENCHMARK_MAT(ctor, cpy<full>, haal);
BENCHMARK_MAT(ctor, cpy<rnd>, haal);

BENCHMARK_MAT(ins_rnd, fil, haal, ratio<1, 4>);
BENCHMARK_MAT(ins_rnd, single, haal, ratio<1, 4>);
BENCHMARK_MAT(ins_rnd, rng<vec>, haal, ratio<1, 4>);
BENCHMARK_MAT(ins_rnd, rng<deq>, haal, ratio<1, 4>);
BENCHMARK_MAT(ins_rnd, rng<unsized>, haal, ratio<1, 4>);

BENCHMARK_MAT(del, single, haal, ratio<1, 2>);
BENCHMARK_MAT(del, rng<full>, haal);
BENCHMARK_MAT(del, rng<rnd>, haal, ratio<1, 2>);

BENCHMARK_MAT(assign, fil<full>, haal, ratio<1, 4>);
BENCHMARK_MAT(assign, fil<rnd>, haal, ratio<1, 4>);
BENCHMARK_MAT(assign, vec<full>, haal, ratio<1, 4>);
BENCHMARK_MAT(assign, vec<rnd>, haal, ratio<1, 4>);
BENCHMARK_MAT(assign, deq<full>, haal, ratio<1, 4>);
BENCHMARK_MAT(assign, deq<rnd>, haal, ratio<1, 4>);
BENCHMARK_MAT(assign, unsized<full>, haal, ratio<1, 4>);
BENCHMARK_MAT(assign, unsized<rnd>, haal, ratio<1, 4>);
BENCHMARK_MAT(assign, cpy_f2f, haal, ratio<1, 4>);
BENCHMARK_MAT(assign, cpy_r2r, haal, ratio<1, 4>);

BENCHMARK_MAT(iter, fwd<rnd>, haal);
BENCHMARK_MAT(iter, fwd<full>, haal);
BENCHMARK_MAT(iter, foreach_<rnd>, haal);
BENCHMARK_MAT(iter, foreach_<full>, haal);
BENCHMARK_MAT(iter, adv<rnd>, haal);
BENCHMARK_MAT(iter, adv<full>, haal);

BENCHMARK_MAT(misc, unique_single, haal);
BENCHMARK_MAT(misc, unique_rand, haal);
BENCHMARK_MAT(misc, erase_if_single, haal);
BENCHMARK_MAT(misc, erase_if_rand, haal);

auto set_contexts = [] {
#ifdef __clang__
    benchmark::AddCustomContext("compiler", "clang-cl");
#else
    benchmark::AddCustomContext("compiler", "msvc");
#endif
    return 0;
}();

BENCHMARK_MAIN();
