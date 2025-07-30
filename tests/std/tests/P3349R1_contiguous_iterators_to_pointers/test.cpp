// Copyright (c) Microsoft Corporation.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include <algorithm>
#include <array>
#include <cassert>
#include <format>
#include <functional>
#include <iterator>
#include <memory>
#include <numeric>
#include <ranges>
#include <span>
#include <vector>

using namespace std;

struct safe_iter_out_of_bounds_err {};

enum range_type { range_full = 0, range_medium = 3, range_small = 4 };

template <class T>
class safe_iter {
public:
    using iterator_concept  = contiguous_iterator_tag;
    using iterator_category = random_access_iterator_tag;
    using value_type        = T;
    using difference_type   = ptrdiff_t;
    using pointer           = T*;
    using reference         = T&;

    constexpr safe_iter(pointer ptr, pointer begin, pointer end) noexcept
        : currentPtr{ptr}, beginPtr{begin}, endPtr{end} {
        assert(currentPtr >= beginPtr && currentPtr <= endPtr);
    }
    constexpr safe_iter() noexcept = default;

    constexpr reference operator*() const {
        if (currentPtr < beginPtr || currentPtr >= endPtr) {
            throw safe_iter_out_of_bounds_err{};
        }
        return *currentPtr;
    }
    constexpr pointer operator->() const noexcept {
        return currentPtr;
    }
    constexpr reference operator[](difference_type n) const {
        return *(*this + n);
    }

    constexpr safe_iter& operator+=(difference_type offset) {
        currentPtr += offset;
        if (currentPtr < beginPtr || currentPtr > endPtr) {
            throw safe_iter_out_of_bounds_err{};
        }
        return *this;
    }
    constexpr safe_iter operator+(difference_type offset) const {
        auto tmp = *this;
        tmp += offset;
        return tmp;
    }
    friend constexpr safe_iter operator+(difference_type offset, const safe_iter& right) {
        return right + offset;
    }
    constexpr safe_iter& operator-=(difference_type offset) {
        return *this += -offset;
    }
    constexpr safe_iter operator-(difference_type offset) const {
        return *this + (-offset);
    }
    constexpr difference_type operator-(const safe_iter& right) const {
        return currentPtr - right.currentPtr;
    }

    constexpr safe_iter& operator++() {
        return *this += 1;
    }
    constexpr safe_iter& operator--() {
        return *this -= 1;
    }
    constexpr safe_iter operator++(int) {
        auto temp = *this;
        ++*this;
        return temp;
    }
    constexpr safe_iter operator--(int) {
        auto temp = *this;
        --*this;
        return temp;
    }

    constexpr bool operator==(const safe_iter& right) const noexcept {
        return currentPtr == right.currentPtr;
    }
    constexpr auto operator<=>(const safe_iter& right) const noexcept {
        return currentPtr <=> right.currentPtr;
    }

    constexpr difference_type operator-(pointer right) const noexcept {
        return currentPtr - right;
    }
    friend constexpr difference_type operator-(pointer left, const safe_iter& right) noexcept {
        return left - right.currentPtr;
    }
    constexpr bool operator==(pointer right) const noexcept {
        return currentPtr == right;
    }
    friend constexpr bool operator==(pointer left, const safe_iter& right) noexcept {
        return left == right.currentPtr;
    }

    static constexpr safe_iter begin(ranges::contiguous_range auto&& rng) noexcept {
        return {to_address(ranges::begin(rng)), to_address(ranges::begin(rng)), to_address(ranges::end(rng))};
    }
    static constexpr safe_iter end(ranges::contiguous_range auto&& rng) noexcept {
        return {to_address(ranges::end(rng)), to_address(ranges::begin(rng)), to_address(ranges::end(rng))};
    }

    static constexpr pair<safe_iter, safe_iter> get_iters(ranges::contiguous_range auto&& rng, range_type type) {
        if (type == range_full) {
            return {safe_iter::begin(rng), safe_iter::end(rng)};
        }

        const auto n = static_cast<underlying_type_t<range_type>>(type);

        // prevent real out-of-bounds access (UB), even if tests fail

        const auto range_dist = ranges::distance(rng);
        const auto first_ptr  = to_address(ranges::begin(rng) + range_dist / n);
        const auto last_ptr   = to_address(ranges::begin(rng) + range_dist * 2 / n);

        return {safe_iter{first_ptr, first_ptr, last_ptr}, safe_iter{last_ptr, first_ptr, last_ptr}};
    }

private:
    pointer currentPtr = nullptr;
    pointer beginPtr   = nullptr;
    pointer endPtr     = nullptr;
};

void single_test_throw(auto&& func) noexcept {
    try {
        func();
        assert(false);
    } catch (const safe_iter_out_of_bounds_err&) {
    }
}
#define THROW_(expr) single_test_throw([&] { (void) (expr); })
#define NTHROW(expr) ([&] noexcept { (void) (expr); }())

template <ranges::contiguous_range ContainerT, ranges::range_size_t<ContainerT> range_size>
void test() {
    using iter       = safe_iter<ranges::range_value_t<ContainerT>>;
    using const_iter = safe_iter<const ranges::range_value_t<ContainerT>>;
    static_assert(contiguous_iterator<iter>);
    static_assert(contiguous_iterator<const_iter>);
    static_assert(range_size >= 12);

    // allow unsafe sentinel
    static_assert(sized_sentinel_for<typename iter::pointer, iter>);
    static_assert(sized_sentinel_for<typename const_iter::pointer, const_iter>);

    const auto container{ranges::to<ContainerT>(
        views::iota(static_cast<iter_value_t<iter>>(0), static_cast<iter_value_t<iter>>(range_size)))};
    assert(ranges::size(container) == range_size);

    const auto [r_first, r_last] = const_iter::get_iters(container, range_medium);
    const auto r_dist            = ranges::distance(r_first, r_last);

    const auto unique_data_container{ranges::to<ContainerT>(
        views::iota(static_cast<iter_value_t<iter>>(range_size), static_cast<iter_value_t<iter>>(range_size * 2)))};
    assert(ranges::size(unique_data_container) == range_size);
    assert(ranges::find_first_of(container, unique_data_container)
           == ranges::end(container)); // ensure that search algorithms examine the entire input range

    const auto [r2_first_small, r2_last_small] = const_iter::get_iters(unique_data_container, range_small);
    const auto [r2_first_big, r2_last_big]     = const_iter::get_iters(unique_data_container, range_full);

    ContainerT container_write_2{container}; // avoid "ranges should not overlap each other"
    ContainerT container_write{container};
    const auto [w_first_small, w_last_small] = iter::get_iters(container_write, range_small);
    const auto w_dist_small                  = ranges::distance(w_first_small, w_last_small);

    const auto [w2_first_big, w2_last_big] = iter::get_iters(container_write_2, range_full);

    const auto iter_sent_test = [&](auto&& func) {
        NTHROW(func(r_first, to_address(r_last)));
        THROW_(func(r_first, to_address(r_last) + 1));
    };
    const auto write_iter_sent_test = [&](auto&& func) {
        NTHROW(func(w_first_small, to_address(w_last_small)));
        THROW_(func(w_first_small, to_address(w_last_small) + 1));
    };

#define TEST__(expr) iter_sent_test([&](auto&& i, auto&& s) { (void) (expr); })
#define WTEST_(expr) write_iter_sent_test([&](auto&& i, auto&& s) { (void) (expr); })

    // [i, s)

    TEST__(ranges::adjacent_find(i, s));
    TEST__(ranges::contains(i, s, unique_data_container[0]));
    TEST__(ranges::contains_subrange(i, s, r2_first_small, r2_last_small));
    TEST__(ranges::contains_subrange(r2_first_big, r2_last_big, i, s));
    TEST__(ranges::count(i, s, unique_data_container[0]));
    TEST__(ranges::ends_with(i, s, i, s));
    TEST__(ranges::equal(i, s, i, s));
    TEST__(ranges::find(i, s, unique_data_container[0]));
    TEST__(ranges::find_end(i, s, r2_first_small, r2_last_small));
    TEST__(ranges::find_end(r2_first_big, r2_last_big, i, s));
    TEST__(ranges::find_first_of(i, s, r2_first_small, r2_last_small));
    TEST__(ranges::find_first_of(r2_first_big, r2_last_big, i, s));
    TEST__(ranges::is_sorted(i, s));
    TEST__(ranges::is_sorted_until(i, s));
    TEST__(ranges::lexicographical_compare(i, s, i, s));
    TEST__(ranges::max(ranges::subrange{i, s}));
    TEST__(ranges::max_element(i, s));
    TEST__(ranges::min(ranges::subrange{i, s}));
    TEST__(ranges::min_element(i, s));
    TEST__(ranges::minmax(ranges::subrange{i, s}));
    TEST__(ranges::minmax_element(i, s));
    TEST__(ranges::mismatch(i, s, i, s));
    TEST__(ranges::search(i, s, r2_first_small, r2_last_small));
    TEST__(ranges::search(r2_first_big, r2_last_big, i, s));
    TEST__(ranges::search_n(i, s, (s - i) / 2, unique_data_container[0]));
    TEST__(ranges::starts_with(i, s, i, s));

    WTEST_(ranges::fill(i, s, container[0]));
    WTEST_(ranges::iota(i, s, container[0]));
    WTEST_(ranges::nth_element(i, i + (s - i) / 2, s));
    WTEST_(ranges::remove(i, s, container[0]));
    WTEST_(ranges::replace(i, s, container[0], container[1]));
    WTEST_(ranges::reverse(i, s));
    WTEST_(ranges::shift_left(i, s, (s - i) / 2));
    WTEST_(ranges::shift_right(i, s, (s - i) / 2));
    WTEST_(ranges::sort(i, s));
    WTEST_(ranges::stable_sort(i, s));
    WTEST_(ranges::unique(i, s));
    
    {
        const auto tests_from_to_algo = [&](auto&& func, auto&& range_func) {
            TEST__(range_func(i, s, iter::begin(container_write)));
            THROW_(func(r_first, r_last, w_first_small));
            THROW_(range_func(r_first, to_address(r_last), w_first_small));
        };
        const auto tests_from_to_algo_backward = [&](auto&& func, auto&& range_func) {
            TEST__(range_func(i, s, iter::end(container_write)));
            THROW_(func(r_first, r_last, w_last_small));
            THROW_(range_func(r_first, to_address(r_last), w_last_small));
        };

#define TEST2_(expr)                                                           \
    tests_from_to_algo([&](auto&& i, auto&& s, auto&& dst) { (void) (expr); }, \
        [&](auto&& i, auto&& s, auto&& dst) { (void) (ranges::expr); })
#define TEST2B(expr)                                                                    \
    tests_from_to_algo_backward([&](auto&& i, auto&& s, auto&& dst) { (void) (expr); }, \
        [&](auto&& i, auto&& s, auto&& dst) { (void) (ranges::expr); })

        // [i, s) -> [dst, ...) / [..., dst)

        TEST2_(copy(i, s, dst));
        TEST2B(copy_backward(i, s, dst));
        TEST2_(move(i, s, dst)); // actually copy
        TEST2B(move_backward(i, s, dst)); // actually copy
        TEST2_(replace_copy(i, s, dst, container[0], container[1]));
        TEST2_(reverse_copy(i, s, dst));
        TEST2_(rotate_copy(i, i + (s - i) / 2, s, dst));

#undef TEST2B
#undef TEST2_

        WTEST_(ranges::swap_ranges(i, s, w2_first_big, to_address(ranges::end(container_write_2))));
        THROW_(swap_ranges(w2_first_big, w2_last_big, w_first_small));
        THROW_(ranges::swap_ranges(
            w2_first_big, to_address(w2_last_big), w_first_small, to_address(ranges::end(container_write))));

        THROW_(adjacent_difference(r_first, r_last, w_first_small, minus<iter_value_t<iter>>{})); // no ranges:: ver.
    }

#undef WTEST_
#undef TEST__

    const auto iter_dist_test = [&](auto&& func) {
        NTHROW(func(r_first, r_dist));
        THROW_(func(r_first, r_dist + 1));
    };
    const auto write_iter_dist_test = [&](auto&& func) {
        NTHROW(func(w_first_small, w_dist_small));
        THROW_(func(w_first_small, w_dist_small + 1));
    };

#define TEST__(expr) iter_dist_test([&](auto&& i, auto&& n) { (void) (expr); })
#define WTEST_(expr) write_iter_dist_test([&](auto&& i, auto&& n) { (void) (expr); })

    // i + [0, n)

    TEST__(copy_n(i, n, iter::begin(container_write)));
    TEST__(ranges::copy_n(i, n, iter::begin(container_write)));

    TEST__(for_each_n(i, n, [](auto&&) noexcept {}));
    TEST__(ranges::for_each_n(i, n, [](auto&&) noexcept {}));

    WTEST_(fill_n(i, n, container[0]));
    WTEST_(ranges::fill_n(i, n, container[0]));

#undef WTEST_
#undef TEST__

    // uninitialized algorithms
    {
        const auto uninit_mem_test = [](auto&& func) {
            using value_type = iter_value_t<iter>;

            array<byte, range_size * sizeof(value_type)> uninit_mem;
            span<value_type> uninit_span{reinterpret_cast<typename iter::pointer>(uninit_mem.data()), range_size};

            const auto [uninit_first_small, uninit_last_small] = iter::get_iters(uninit_span, range_small);

            func(uninit_first_small, uninit_last_small);

            destroy(uninit_first_small, uninit_last_small);
        };
        const auto uninit_mem_test_tmp = [&](auto&& func) {
            uninit_mem_test([&](auto fst, auto lst) {
                auto container_temp{container};
                const auto [tmp_first, tmp_last] = iter::get_iters(container_temp, range_medium);

                func(fst, lst, tmp_first, tmp_last);
            });
        };

        uninit_mem_test([&](auto fst, auto lst) {
            THROW_(uninitialized_copy(r_first, r_last, fst));
            THROW_(ranges::uninitialized_copy(r_first, to_address(r_last), fst, to_address(lst) + 1));
            NTHROW(ranges::uninitialized_copy(r_first, to_address(r_last), fst, to_address(lst)));
        });
        uninit_mem_test([&](auto fst, auto lst) {
            THROW_(uninitialized_copy_n(r_first, r_dist, fst));
            THROW_(uninitialized_copy_n(r_first, r_dist + 1, to_address(fst)));
            THROW_(ranges::uninitialized_copy_n(r_first, r_dist, fst, to_address(lst) + 1));
            THROW_(ranges::uninitialized_copy_n(r_first, r_dist + 1, fst, to_address(lst)));
            NTHROW(ranges::uninitialized_copy_n(r_first, r_dist, fst, to_address(lst)));
        });
        uninit_mem_test([&](auto fst, auto lst) {
            THROW_(ranges::uninitialized_fill(fst, to_address(lst) + 1, container[0]));
            NTHROW(ranges::uninitialized_fill(fst, to_address(lst), container[0]));
        });
        uninit_mem_test([&](auto fst, auto lst) {
            const auto dist = ranges::distance(fst, lst);

            THROW_(uninitialized_fill_n(fst, dist + 1, container[0]));
            THROW_(uninitialized_fill_n(fst + 1, dist, container[0]));
            THROW_(ranges::uninitialized_fill_n(fst, dist + 1, container[0]));
            THROW_(ranges::uninitialized_fill_n(fst + 1, dist, container[0]));
            NTHROW(ranges::uninitialized_fill_n(fst, dist, container[0]));
        });
        uninit_mem_test_tmp([](auto fst, auto lst, auto first, auto last) {
            THROW_(uninitialized_move(first, last, fst));
            THROW_(ranges::uninitialized_move(first, to_address(last), fst, to_address(lst) + 1));
            NTHROW(ranges::uninitialized_move(first, to_address(last), fst, to_address(lst)));
        });
        uninit_mem_test_tmp([](auto fst, auto lst, auto first, auto last) {
            const auto dist = ranges::distance(first, last);

            THROW_(uninitialized_move_n(first, dist, fst));
            THROW_(uninitialized_move_n(first, dist + 1, to_address(fst)));
            THROW_(ranges::uninitialized_move_n(first, dist, fst, to_address(lst) + 1));
            THROW_(ranges::uninitialized_move_n(first, dist + 1, fst, to_address(lst)));
            NTHROW(ranges::uninitialized_move_n(first, dist, fst, to_address(lst)));
        });
    }

    // format {:s} & string_view
    {
        const auto chars = container
                         | views::transform([](auto&& value) { return static_cast<char>(value % 26 + 'A'); })
                         | ranges::to<vector<char>>();

        const auto [chars_first, chars_last] = safe_iter<const char>::get_iters(chars, range_medium);

        const ranges::subrange good_range{chars_first, to_address(chars_last)};
        const ranges::subrange bad_range{chars_first, to_address(chars_last) + 1};

        static_assert(ranges::contiguous_range<decltype(good_range)>);
        static_assert(ranges::contiguous_range<decltype(bad_range)>);

        NTHROW(format("{:s}", good_range));
        THROW_(format("{:s}", bad_range));

        NTHROW((string_view{chars_first, to_address(chars_last)}));
        THROW_((string_view{chars_first, to_address(chars_last) + 1}));
    }

    NTHROW(views::counted(r_first, r_dist));
    THROW_(views::counted(r_first, r_dist + 1));

    NTHROW((span{r_first, to_address(r_last)}));
    NTHROW((span{r_first, static_cast<size_t>(r_dist)}));
    THROW_((span{r_first, to_address(r_last) + 1}));
    THROW_((span{r_first, static_cast<size_t>(r_dist + 1)}));
}

consteval void constexpr_test(ranges::contiguous_range auto&& rng) {
    span{ranges::begin(rng), ranges::end(rng)};
    span{ranges::begin(rng), ranges::size(rng)};
    string_view{ranges::begin(rng), ranges::end(rng)};

    using iter = safe_iter<char>;

    span{iter::begin(rng), iter::end(rng)};
    span{iter::begin(rng), to_address(iter::end(rng))};
    span{iter::begin(rng), ranges::size(rng)};
    string_view{iter::begin(rng), to_address(iter::end(rng))};
}

int main() {
    test<vector<int32_t>, 12>();
    test<vector<int32_t>, 256>(); // triggers vectorization

    test<vector<int64_t>, 12>();
    test<vector<int64_t>, 256>();

    test<vector<int16_t>, 12>();
    test<vector<int16_t>, 256>();

    static_assert(string{}.capacity() >= 12 && string{}.capacity() < 63);

    test<string, 12>(); // SSO
    test<string, 63>();

    constexpr_test(string(12, 'x')); // SSO
    constexpr_test(string(256, 'x'));
    constexpr_test(vector<char>(256));

    // remove_copy & unique_copy
    {
        using iter       = safe_iter<int>;
        using const_iter = safe_iter<const int>;

        const auto src = {1, 2, 3, 4, 4, 5, 5};

        const auto src_first    = const_iter::begin(src);
        const auto src_last     = const_iter::end(src);
        const auto src_last_ptr = to_address(src_last);

        array<int, 5 + 1> dst;
        const iter dst_first{
            to_address(ranges::begin(dst)), to_address(ranges::begin(dst)), to_address(ranges::begin(dst) + 5)};

        NTHROW(remove_copy(src_first, src_last, dst_first, 5));
        NTHROW(unique_copy(src_first, src_last, dst_first));
        THROW_(remove_copy(src_first, src_last, dst_first, 1));
        THROW_(unique_copy(src_first, src_last, dst_first + 1));
        NTHROW(ranges::remove_copy(src_first, src_last_ptr, dst_first, 5));
        NTHROW(ranges::unique_copy(src_first, src_last_ptr, dst_first));
        THROW_(ranges::remove_copy(src_first, src_last_ptr, dst_first, 1));
        THROW_(ranges::unique_copy(src_first, src_last_ptr, dst_first + 1));
    }

    return 0;
}
