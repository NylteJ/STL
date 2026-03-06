// Copyright (c) Microsoft Corporation.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#define min(a, b) delete
#define max(a, b) delete

// TODO: These `#include`s are from the final version and not all used yet.
#include <algorithm>
#include <array>
#include <cassert>
#include <compare>
#include <concepts>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <functional>
#include <hive>
#include <initializer_list>
#include <iterator>
#include <limits>
#include <list>
#include <memory>
#include <memory_resource>
#include <new>
#include <optional>
#include <random>
#include <ranges>
#include <span>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <vector>

#undef max
#undef min

using namespace std;

struct evil_type {
    void operator&() const = delete;

    template <class Other>
    void operator,(const Other&) const
        requires (!is_same_v<evil_type, Other>)
    = delete;
    friend void operator,(const auto&, const evil_type&) = delete;
};

namespace wrappers {
    struct wrapper_base {};
    template <class T>
    concept wrapper = derived_from<T, wrapper_base>;

    template <class T>
    struct __declspec(empty_bases) nontrivial final : wrapper_base, evil_type {
        T value;

        /* implicit */ nontrivial(T unwrapped) : value(unwrapped) {}

        explicit nontrivial() : value() {}
        nontrivial(const nontrivial& other) : value(other.value) {}
        nontrivial(nontrivial&& other) noexcept(false) : value(move(other.value)) {}
        nontrivial& operator=(const nontrivial& right) {
            value = right.value;
            return *this;
        }
        nontrivial& operator=(nontrivial&& right) noexcept(false) {
            value = move(right.value);
            return *this;
        }
        ~nontrivial() noexcept {}
    };

    template <class T>
    struct move_only : wrapper_base {
        T value;

        move_only() = default;
        /* implicit */ move_only(T unwrapped) : value(unwrapped) {}

        move_only(const move_only&)            = delete;
        move_only(move_only&&)                 = default;
        move_only& operator=(const move_only&) = delete;
        move_only& operator=(move_only&&)      = default;
    };

    template <class T>
    struct pinned : wrapper_base {
        T value;

        pinned() = default;
        /* implicit */ pinned(T unwrapped) : value(unwrapped) {}

        pinned(const pinned&)            = delete;
        pinned(pinned&&)                 = delete;
        pinned& operator=(const pinned&) = delete;
        pinned& operator=(pinned&&)      = delete;
    };

    namespace details {
        struct secret_ctor_tag {};
    } // namespace details
    template <class T>
    struct tagged_constructible : wrapper_base {
        using tag = details::secret_ctor_tag;

        T value;

        /* implicit */ tagged_constructible(T unwrapped) : value(unwrapped) {}

        template <class... Args>
        explicit tagged_constructible(tag, Args&&... args)
            requires (is_constructible_v<T, Args && ...>)
            : value(forward<Args>(args)...) {}

        tagged_constructible(tag, const tagged_constructible& other) : value(other.value) {}
        tagged_constructible(tag, tagged_constructible&& other) : value(move(other.value)) {}

        tagged_constructible(const tagged_constructible&) {
            // static_assert rather than =delete because container-compatible-range requires this
            static_assert(false);
        }
        tagged_constructible(tagged_constructible&&) {
            // static_assert rather than =delete because container-compatible-range requires this
            static_assert(false);
        }
        tagged_constructible& operator=(const tagged_constructible&) = default;
        tagged_constructible& operator=(tagged_constructible&&)      = default;

        friend void swap(tagged_constructible& left, tagged_constructible& right) noexcept {
            swap(left.value, right.value);
        }
    };

    constexpr auto unwrap_equal_pred = [](const wrapper auto& left, const wrapper auto& right) -> bool {
        return left.value == right.value;
    };
    constexpr auto unwrap_less_pred = [](const wrapper auto& left, const wrapper auto& right) -> bool {
        return right.value > left.value; // `left.value < right.value` will confuse EDG
    };
} // namespace wrappers
template <wrappers::wrapper Wrapper>
auto unwrap(const Wrapper& wrapper) {
    return wrapper.value;
}
template <semiregular T>
    requires (!wrappers::wrapper<T>)
T unwrap(const T& val) {
    return val;
}

template <ranges::input_range Range>
decltype(auto) unwrap_range(Range&& rng) {
    using rg_value_t = ranges::range_value_t<Range>;
    if constexpr (is_same_v<decltype(unwrap(declval<rg_value_t>())), rg_value_t>) {
        return forward<Range>(rng);
    } else {
        return forward<Range>(rng) | views::transform([](const auto& val) { return unwrap(val); });
    }
}

namespace allocators {
    template <class T>
    struct tagged_allocator : allocator<T> {
        tagged_allocator() = default;
        template <class U>
        constexpr explicit tagged_allocator(const tagged_allocator<U>&) noexcept {}

        template <class... Args>
        constexpr void construct(T* p, Args&&... args)
            requires requires { typename T::tag; }
        {
            construct_at(p, typename T::tag{}, forward<Args>(args)...);
        }
    };

    template <class T, class ElemT>
    struct custom_allocator;
    namespace details {
        template <class T, class U>
        concept same_without_const = is_same_v<remove_const_t<T>, remove_const_t<U>>;

        template <class T>
        struct fancy_pointer_usings {
            using iterator_concept  = contiguous_iterator_tag;
            using iterator_category = random_access_iterator_tag;
            using value_type        = T;
            using difference_type   = ptrdiff_t;
            using pointer           = T*;
            using reference         = T&;
        };
        template <class Void>
            requires (is_void_v<Void>)
        struct fancy_pointer_usings<Void> {
        protected:
            using difference_type = ptrdiff_t;
            using reference       = int&;
        };

        template <class T>
        class fancy_pointer : public fancy_pointer_usings<T>, public evil_type {
            using mybase = fancy_pointer_usings<T>;
            using typename mybase::difference_type, typename mybase::reference;

        public:
            constexpr fancy_pointer() noexcept = default;
            constexpr fancy_pointer(nullptr_t) noexcept : ptr{nullptr} {}

            constexpr explicit fancy_pointer(const fancy_pointer<const void>& other) noexcept
                requires (is_const_v<T> && !is_void_v<T>)
                : ptr{static_cast<T*>(other.ptr)} {}
            constexpr explicit fancy_pointer(const fancy_pointer<void>& other) noexcept
                requires (!is_void_v<T>)
                : ptr{static_cast<T*>(other.ptr)} {}

            operator fancy_pointer<const T>() const noexcept
                requires (!is_const_v<T>)
            {
                return fancy_pointer<const T>{ptr};
            }
            operator fancy_pointer<void>() const noexcept
                requires (!is_void_v<T> && !is_const_v<T>)
            {
                return fancy_pointer<void>{ptr};
            }
            operator fancy_pointer<const void>() const noexcept
                requires (!is_void_v<T> || !is_const_v<T>)
            {
                return fancy_pointer<const void>{ptr};
            }

            explicit operator bool() const noexcept {
                return static_cast<bool>(ptr);
            }

            constexpr reference operator*() const
                requires (!is_void_v<T>)
            {
                return *ptr;
            }
            constexpr T* operator->() const
                requires (!is_void_v<T>)
            {
                return addressof(*ptr);
            }

            void operator->*(const auto&) const = delete;

            constexpr fancy_pointer& operator++()
                requires (!is_void_v<T>)
            {
                ++ptr;
                return *this;
            }
            constexpr fancy_pointer operator++(int)
                requires (!is_void_v<T>)
            {
                const auto tmp = *this;
                ++*this;
                return tmp;
            }
            constexpr fancy_pointer& operator--()
                requires (!is_void_v<T>)
            {
                --ptr;
                return *this;
            }
            constexpr fancy_pointer operator--(int)
                requires (!is_void_v<T>)
            {
                const auto tmp = *this;
                --*this;
                return tmp;
            }

            constexpr fancy_pointer& operator+=(difference_type n) noexcept
                requires (!is_void_v<T>)
            {
                ptr += n;
                return *this;
            }
#ifdef _WIN64
            constexpr fancy_pointer& operator+=(int n) noexcept
                requires (!is_void_v<T>)
            {
                ptr += n;
                return *this;
            }
#endif // _WIN64
            constexpr fancy_pointer& operator-=(difference_type n) noexcept
                requires (!is_void_v<T>)
            {
                ptr -= n;
                return *this;
            }

            constexpr fancy_pointer operator+(difference_type n) const noexcept
                requires (!is_void_v<T>)
            {
                return fancy_pointer{ptr + n};
            }
#ifdef _WIN64
            constexpr fancy_pointer operator+(int n) const noexcept
                requires (!is_void_v<T>)
            {
                return fancy_pointer{ptr + n};
            }
#endif // _WIN64
            constexpr friend fancy_pointer operator+(difference_type n, fancy_pointer ptr) noexcept
                requires (!is_void_v<T>)
            {
                return ptr += n;
            }
            constexpr fancy_pointer operator-(difference_type n) const noexcept
                requires (!is_void_v<T>)
            {
                return fancy_pointer{ptr - n};
            }

            constexpr reference operator[](difference_type off) const noexcept {
                return ptr[off];
            }

            template <same_without_const<T> U>
            constexpr bool operator==(const fancy_pointer<U>& other) const noexcept {
                return ptr == other.ptr;
            }
            constexpr bool operator==(nullptr_t) const noexcept {
                return ptr == nullptr;
            }

            template <same_without_const<T> U>
            constexpr bool operator<(const fancy_pointer<U>& other) const noexcept
                requires (!is_void_v<T>)
            {
                return ptr < other.ptr;
            }
            template <same_without_const<T> U>
            constexpr bool operator<=(const fancy_pointer<U>& other) const noexcept
                requires (!is_void_v<T>)
            {
                return ptr <= other.ptr;
            }
            template <same_without_const<T> U>
            constexpr bool operator>(const fancy_pointer<U>& other) const noexcept
                requires (!is_void_v<T>)
            {
                return ptr > other.ptr;
            }
            template <same_without_const<T> U>
            constexpr bool operator>=(const fancy_pointer<U>& other) const noexcept
                requires (!is_void_v<T>)
            {
                return ptr >= other.ptr;
            }

            template <same_without_const<T> U>
            constexpr difference_type operator-(const fancy_pointer<U>& other) const noexcept
                requires (!is_void_v<T>)
            {
                return ptr - other.ptr;
            }

        private:
            template <class U>
            friend class fancy_pointer;

            template <class T_, class ElemT>
            friend struct allocators::custom_allocator;
            friend std::pointer_traits<fancy_pointer>;

            constexpr explicit fancy_pointer(T* ptr_) noexcept : ptr{ptr_} {}

            T* ptr;
        };
    } // namespace details
} // namespace allocators

template <class T>
    requires (!is_void_v<T>)
struct std::pointer_traits<allocators::details::fancy_pointer<T>> {
    using pointer         = allocators::details::fancy_pointer<T>;
    using element_type    = T;
    using difference_type = allocators::details::fancy_pointer<T>::difference_type;

    template <class U>
    using rebind = allocators::details::fancy_pointer<U>;

    static constexpr pointer pointer_to(element_type& ref) noexcept {
        return pointer{addressof(ref)};
    }
    static constexpr element_type* to_address(const pointer& ptr) noexcept {
        return ptr.ptr;
    }
};

namespace allocators {
    template <class T, class ElemT = T>
    struct custom_allocator final {
        using value_type = T;
        using pointer    = details::fancy_pointer<T>;

        custom_allocator() = default;
        template <class U>
        constexpr explicit custom_allocator(const custom_allocator<U, ElemT>&) noexcept {}

        constexpr pointer allocate(size_t cnt) {
            return pointer{allocator<T>{}.allocate(cnt)};
        }
        constexpr void deallocate(pointer ptr, size_t cnt) noexcept {
            allocator<T>{}.deallocate(ptr.ptr, cnt);
        }

        template <class... Args>
        constexpr void construct(T* p, Args&&... args) {
            static_assert(is_same_v<T, ElemT>,
                "`construct` and `destroy` are called only for the container's element type, not "
                "for internal types used by the container ([container.requirements.pre]/3).");
            construct_at(p, forward<Args>(args)...);
        }
        constexpr void destroy(T* p) {
            static_assert(is_same_v<T, ElemT>,
                "`construct` and `destroy` are called only for the container's element type, not "
                "for internal types used by the container ([container.requirements.pre]/3).");
            destroy_at(p);
        }

        constexpr bool operator==(const custom_allocator&) const {
            return true;
        }
    };

    struct small_allocator_res {
        // `difference_type` must be able to represent the difference between any two pointers in the allocation model
        // ([allocator.requirements.general]/14)
        array<char, numeric_limits<int16_t>::max()> buffer;
        void* current          = buffer.data();
        size_t allocated_count = 0;

        void* allocate(size_t bytes, size_t align_) {
            auto free_bytes = buffer.size() - (static_cast<char*>(current) - buffer.data());
            if (!align(align_, bytes, current, free_bytes)) {
                throw bad_alloc{};
            }

            const auto ret = current;
            current        = static_cast<char*>(current) + bytes;
            ++allocated_count;
            return ret;
        }
        void deallocate() noexcept {
            --allocated_count;
            if (allocated_count == 0) {
                current = buffer.data();
            }
        }
    };
    template <class T>
    struct small_allocator {
        using value_type      = T;
        using size_type       = uint16_t;
        using difference_type = int16_t;

        small_allocator_res* res;

        constexpr explicit small_allocator(small_allocator_res& res_) noexcept : res(&res_) {}
        template <class U>
        constexpr explicit small_allocator(const small_allocator<U>& other) noexcept : res(other.res) {}

        constexpr T* allocate(size_t cnt) {
            return static_cast<T*>(res->allocate(cnt * sizeof(T), alignof(T)));
        }
        constexpr void deallocate(T*, size_t) noexcept {
            res->deallocate();
        }

        constexpr size_type max_size() const noexcept {
            return static_cast<size_type>(
                res->buffer.max_size() / sizeof(T) / 3); // smaller than theoretical max to test splicing of large hives
        }

        constexpr bool operator==(const small_allocator&) const = default;
    };
} // namespace allocators

template <class Alloc, class Maker, class T = Alloc::value_type,
    class EqualPred = conditional_t<wrappers::wrapper<T>, decltype(wrappers::unwrap_equal_pred), equal_to<T>>,
    class LessPred  = conditional_t<wrappers::wrapper<T>, decltype(wrappers::unwrap_less_pred), less<T>>>
class tests {
private:
    using hive_t   = hive<T, Alloc>;
    using ptr_t    = hive_t::pointer;
    using cptr_t   = hive_t::const_pointer;
    using iter_t   = hive_t::iterator;
    using riter_t  = hive_t::reverse_iterator;
    using citer_t  = hive_t::const_iterator;
    using criter_t = hive_t::const_reverse_iterator;
    using diff_t   = hive_t::difference_type;
    using size_ty  = hive_t::size_type;

    using al_traits = allocator_traits<Alloc>;

    static constexpr bool tagged_al = is_same_v<Alloc, allocators::tagged_allocator<T>>;
    using tag_t                     = decltype([] {
        if constexpr (tagged_al) {
            return typename T::tag{};
        }
    }());

    static constexpr bool small_al = sizeof(size_ty) <= sizeof(uint16_t);

    static constexpr bool has_default_al = is_default_constructible_v<Alloc>;
    static constexpr bool different_al   = !al_traits::is_always_equal::value;

    static constexpr bool Cpp17MoveInsertable =
        tagged_al ? is_constructible_v<T, tag_t, T&&> : is_move_constructible_v<T>;
    static constexpr bool Cpp17CopyInsertable =
        tagged_al ? is_constructible_v<T, tag_t, const T&> : is_copy_constructible_v<T>;
    static constexpr bool Cpp17DefaultInsertable =
        tagged_al ? is_constructible_v<T, tag_t> : is_default_constructible_v<T>;
    static constexpr bool Cpp17CopyAssignable = is_copy_assignable_v<T>;
    static constexpr bool Cpp17MoveAssignable = is_move_assignable_v<T>;
    static constexpr bool Cpp17Swappable      = is_swappable_v<T>;

    Alloc al_1;
    Alloc al_2;

    Maker raw_range_maker;

    EqualPred equal_pred;
    LessPred less_pred;

    mt19937_64 rand_engine;

    using raw_range_t = decltype(raw_range_maker(0, rand_engine));
    static_assert(ranges::forward_range<raw_range_t>);
    using raw_value_t = ranges::range_value_t<raw_range_t>;
    static_assert(regular<raw_value_t>);
    static_assert(three_way_comparable<raw_value_t>);
    static_assert(is_same_v<raw_value_t, decltype(unwrap(declval<T>()))>);
    static_assert(convertible_to<raw_value_t, T>);
    static_assert(sizeof(raw_value_t) == sizeof(T));

public:
    tests(Alloc alloc_1, Alloc alloc_2, Maker raw_rng_maker, uint64_t random_seed = 142857,
        EqualPred equal_pred_ = EqualPred(), LessPred less_pred_ = LessPred())
        : al_1(alloc_1), al_2(alloc_2), raw_range_maker(raw_rng_maker), equal_pred(equal_pred_), less_pred(less_pred_),
          rand_engine(random_seed) {
        if constexpr (different_al) {
            assert(al_1 != al_2);
        }
    }

private:
    raw_range_t gen_raw_rng(integral auto cnt) {
        return raw_range_maker(cnt, rand_engine);
    }
    raw_value_t gen_raw_value() {
        auto tmp = raw_range_maker(1, rand_engine);
        return *ranges::begin(tmp);
    }

    static void assert_limits(const hive_t& cont, hive_limits expect) {
        const auto limits = cont.block_capacity_limits();
        assert(limits.min == expect.min && limits.max == expect.max);
    }

    template <ranges::input_range Expected>
    void assert_equal(const hive_t& cont, Expected&& expect) {
        using expected_value_t = ranges::range_value_t<Expected>;
        if constexpr (is_same_v<expected_value_t, T>) {
            assert(ranges::equal(cont, expect, equal_pred));
        } else {
            static_assert(is_same_v<expected_value_t, raw_value_t>);
            assert(ranges::equal(unwrap_range(cont), expect));
        }
    }
    template <ranges::input_range Expected>
    void assert_permutation(const hive_t& cont, Expected&& expect) {
        if constexpr (ranges::forward_range<Expected>) {
            using expected_value_t = ranges::range_value_t<Expected>;
            if constexpr (is_same_v<expected_value_t, T>) {
                assert(ranges::is_permutation(cont, expect, equal_pred));
            } else {
                static_assert(is_same_v<expected_value_t, raw_value_t>);
                assert(ranges::is_permutation(unwrap_range(cont), expect));
            }
        } else {
            assert(ranges::is_permutation(
                unwrap_range(cont), unwrap_range(forward<Expected>(expect)) | ranges::to<vector>()));
        }
    }

public:
    static consteval bool static_test() {
        // TODO...

        return true;
    }

    void test_all() {
        static_assert(static_test());

        // TODO...
    }
};

template <class Raw>
constexpr auto maker = [](integral auto cnt, uniform_random_bit_generator auto& rnd_engine) {
    const auto single_maker = [&] {
        if constexpr (is_integral_v<Raw>) {
            static_assert(is_unsigned_v<Raw>);
            return static_cast<Raw>(rnd_engine());
        } else {
            using value_t = ranges::range_value_t<Raw>;
            static_assert(is_unsigned_v<value_t>);
            static_assert(is_same_v<Raw, array<value_t, sizeof(Raw) / sizeof(value_t)>>);
            Raw ret;
            ranges::generate(ret, [&] { return static_cast<value_t>(rnd_engine()); });
            return ret;
        }
    };

    vector<Raw> ret(static_cast<size_t>(cnt));
    ranges::generate(ret, single_maker);
    return ret;
};

template <class T, class Oper, class... Args>
void allocator_matrix(Oper oper, Args&&... args) {
    using namespace allocators;

    oper(tests{allocator<T>{}, allocator<T>{}, args...});

    static_assert(decltype(tests{custom_allocator<T>{}, custom_allocator<T>{}, args...})::static_test());

    {
        const auto res_1 = make_unique<small_allocator_res>();
        const auto res_2 = make_unique<small_allocator_res>();
        oper(tests{small_allocator<T>{*res_1}, small_allocator<T>{*res_2}, args...});
    }
}

template <class Raw>
void test_matrix() {
    constexpr auto test_all    = [](auto&& test) { test.test_all(); };
    constexpr auto static_test = []<class T>(const T&) { static_assert(T::static_test()); };

    using namespace wrappers;

    allocator_matrix<Raw>(test_all, maker<Raw>, 42u);
    allocator_matrix<nontrivial<Raw>>(test_all, maker<Raw>, 123456u);

    allocator_matrix<move_only<Raw>>(static_test, maker<Raw>);
    allocator_matrix<pinned<Raw>>(static_test, maker<Raw>);

    static_assert(tests<allocators::tagged_allocator<tagged_constructible<Raw>>, decltype(maker<Raw>)>::static_test());
}

using trivial_medium = uint16_t; // small skipfield
using trivial_large  = uint64_t; // big skipfield

int main() {
    test_matrix<trivial_medium>();
    test_matrix<trivial_large>();

#ifndef __EDG__
    // sizeof(_Union) > sizeof(_Ty)
    {
        using value_type = array<uint8_t, 5>;
        static_assert(sizeof(_Hive_union_provider<value_type>::_Union) > sizeof(value_type));
        const allocator<value_type> al{};
        tests{al, al, maker<value_type>}.test_all();
    }
#endif // !defined(__EDG__)
}
