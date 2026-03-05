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

#define DO_IF_VALID(expr)               \
    if constexpr (requires { expr; }) { \
        expr;                           \
    }

template <class B>
concept boolean_testable_impl = convertible_to<B, bool>;
template <class B>
concept boolean_testable = boolean_testable_impl<B> && requires(B&& b) {
    { !forward<B>(b) } -> boolean_testable_impl;
};

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

    template <class T>
    struct max_size_0_allocator {
        using value_type = T;

        max_size_0_allocator() = default;
        template <class U>
        explicit max_size_0_allocator(max_size_0_allocator<U>) {}

        size_t max_size() const noexcept {
            return 0;
        }
        T* allocate(size_t) {
            throw bad_alloc{};
        }
        void deallocate(T*, size_t) noexcept {
            assert(false);
        }

        bool operator==(const max_size_0_allocator&) const = default;
    };
} // namespace allocators

template <class Ref, class Alloc, derived_from<input_iterator_tag> IterConcept, bool Common, bool SizedRange,
    bool SizedSent>
class custom_range {
private:
    static constexpr bool is_forward = derived_from<IterConcept, forward_iterator_tag>;
    static constexpr bool is_bidi    = derived_from<IterConcept, bidirectional_iterator_tag>;
    static constexpr bool is_random  = derived_from<IterConcept, random_access_iterator_tag>;
    static constexpr bool is_ctg     = derived_from<IterConcept, contiguous_iterator_tag>;

    static_assert(is_reference_v<Ref>);
    static_assert(!is_same_v<remove_cvref_t<Ref>, bool>);
    static_assert(SizedRange >= SizedSent);
    static_assert(SizedSent >= is_random);

    using al_traits = allocator_traits<Alloc>;

public:
    using value_type     = remove_cvref_t<Ref>;
    using allocator_type = Alloc;
    using pointer        = al_traits::pointer;
    using const_pointer  = al_traits::const_pointer;
    using reference      = Ref;
    using const_reference =
        conditional_t<is_lvalue_reference_v<Ref>, const remove_reference_t<Ref>&, const remove_reference_t<Ref>&&>;
    using size_type       = al_traits::size_type;
    using difference_type = al_traits::difference_type;

private:
    class sent : public evil_type {
    public:
        sent() = default;

    private:
        friend custom_range;

        constexpr explicit sent(const value_type* ptr_) noexcept : ptr(ptr_) {}

        const value_type* ptr;
    };

    template <bool Const>
    class iter : public evil_type {
    public:
        using iterator_concept  = IterConcept;
        using iterator_category = conditional_t<is_ctg, random_access_iterator_tag, IterConcept>;
        using value_type        = custom_range::value_type;
        using difference_type   = ptrdiff_t;
        using pointer           = conditional_t<Const, const value_type*, value_type*>;
        using reference         = conditional_t<Const, custom_range::const_reference, custom_range::reference>;

        iter() = default;

        /* implicit */ constexpr operator iter<true>() const noexcept
            requires (!Const)
        {
            return iter<true>{ptr};
        }

        constexpr reference operator*() const noexcept {
            return static_cast<reference>(*ptr);
        }
        constexpr pointer operator->() const noexcept {
            return ptr;
        }

        constexpr iter& operator++() noexcept {
            ++ptr;
            return *this;
        }
        constexpr iter operator++(int) noexcept {
            const auto tmp = *this;
            ++ptr;
            return tmp;
        }

        constexpr iter& operator--() noexcept
            requires is_bidi
        {
            --ptr;
            return *this;
        }
        constexpr iter operator--(int) noexcept
            requires is_bidi
        {
            const auto tmp = *this;
            --ptr;
            return tmp;
        }

        constexpr iter& operator+=(const ptrdiff_t off) noexcept
            requires is_random
        {
            ptr += off;
            return *this;
        }
        constexpr iter& operator-=(const ptrdiff_t off) noexcept
            requires is_random
        {
            ptr -= off;
            return *this;
        }
        constexpr reference operator[](const difference_type off) const noexcept
            requires is_random
        {
            return static_cast<reference>(ptr[off]);
        }

        constexpr difference_type operator-(const iter& right) const noexcept
            requires (SizedSent && (Common || is_random))
        {
            return ptr - right.ptr;
        }
        constexpr difference_type operator-(const sent& right) const noexcept
            requires (SizedSent && !Common)
        {
            return ptr - right.ptr;
        }

        constexpr bool operator==(const iter& right) const noexcept
            requires (Common || is_forward)
        {
            return ptr == right.ptr;
        }
        constexpr bool operator==(const sent& right) const noexcept
            requires (!Common)
        {
            return ptr == right.ptr;
        }

        constexpr bool operator<(const iter& right) const noexcept
            requires is_random
        {
            return ptr < right.ptr;
        }
        constexpr bool operator<=(const iter& right) const noexcept
            requires is_random
        {
            return ptr <= right.ptr;
        }
        constexpr bool operator>(const iter& right) const noexcept
            requires is_random
        {
            return ptr > right.ptr;
        }
        constexpr bool operator>=(const iter& right) const noexcept
            requires is_random
        {
            return ptr >= right.ptr;
        }

        constexpr iter operator+(const difference_type off) const noexcept
            requires is_random
        {
            auto tmp = *this;
            tmp += off;
            return tmp;
        }
        constexpr iter operator-(const difference_type off) const noexcept
            requires is_random
        {
            auto tmp = *this;
            tmp -= off;
            return tmp;
        }
        friend constexpr iter operator+(const difference_type off, iter it) noexcept
            requires is_random
        {
            it += off;
            return it;
        }

    private:
        friend custom_range;

        constexpr explicit iter(pointer ptr_) noexcept : ptr(ptr_) {}

        pointer ptr;
    };

public:
    using iterator       = iter<false>;
    using const_iterator = iter<true>;

    template <class Rng>
    custom_range(from_range_t, Rng&& rng, Alloc al = Alloc()) : values(from_range, forward<Rng>(rng), al) {}

    iterator begin() noexcept {
        if constexpr (!is_forward) {
            assert(!begin_has_been_called);
            begin_has_been_called = true;
        }
        return iterator{values.data()};
    }
    const_iterator begin() const noexcept
        requires is_forward
    {
        return const_iterator{values.data()};
    }
    iterator end() noexcept
        requires Common
    {
        return iterator{values.data() + values.size()};
    }
    auto end() const noexcept {
        return conditional_t<Common, const_iterator, sent>{values.data() + values.size()};
    }

    size_type size() noexcept
        requires SizedRange
    {
        if constexpr (!is_forward) {
            assert(!begin_has_been_called);
        }
        return values.size();
    }

private:
    vector<value_type, Alloc> values;
    bool begin_has_been_called = false;
};

template <class Pred>
struct counted_pred {
    Pred pred;
    size_t cnt = 0;

    explicit counted_pred(const Pred& pr) : pred(pr) {}

    counted_pred(const counted_pred&)            = delete;
    counted_pred& operator=(const counted_pred&) = delete;

    template <class... Args>
    decltype(auto) operator()(Args&&... args) {
        ++cnt;
        return pred(forward<Args>(args)...);
    }
};

template <class Exception, class Fn>
void assert_throw(Fn func) noexcept {
    try {
        func();
        assert(false && "should throw, but returned");
    } catch (const Exception&) {
    }
}

namespace EH {
    template <class T>
    struct EH_allocator;
    template <class T>
    struct wrapper;

    void forbid_alloc();
    void allow_alloc();
} // namespace EH

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

    static constexpr bool EH_al = is_same_v<Alloc, EH::EH_allocator<T>>;

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

    static constexpr bool EH_wrapper = is_same_v<T, EH::wrapper<raw_value_t>>;

    static constexpr array limits_counts_mat = [] {
        using lim    = hive_limits;
        using counts = array<size_ty, 4>;
        if constexpr (!small_al) {
            return array{
                pair{lim{3, 12}, counts{0, 1, 8, 20}},
                pair{lim{8, 45}, counts{0, 3, 42, 60}},
                pair{lim{32, 80}, counts{0, 6, 50, 100}},

                pair{lim{8, 8}, counts{0, 1, 8, 20}},
                pair{lim{42, 42}, counts{0, 3, 42, 60}},
                pair{lim{50, 50}, counts{0, 6, 50, 100}},

                pair{lim{1, 1}, counts{0, 1, 8, 20}},
            };
        } else {
            return array{
                pair{lim{2, 5}, counts{0, 1, 3, 6}},
                pair{lim{4, 10}, counts{0, 2, 5, 11}},
                pair{lim{9, 16}, counts{0, 3, 12, 19}},

                pair{lim{3, 3}, counts{0, 1, 3, 6}},
                pair{lim{5, 5}, counts{0, 2, 5, 11}},
                pair{lim{12, 12}, counts{0, 3, 12, 19}},

                pair{lim{1, 1}, counts{0, 1, 3, 6}},
            };
        }
    }();

    static constexpr array limits_counts_mat_reduced = {
        limits_counts_mat[0],
        limits_counts_mat[1],
        limits_counts_mat[2],
    };

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

    static vector<citer_t> get_hive_nonend_iters(const hive_t& cont) {
        vector<citer_t> ret(cont.size());
        auto it = cont.begin();
        for (size_t i = 0; i != cont.size(); ++i) {
            ret[i] = it;
            ++it;
        }
        return ret;
    }

    static vector<raw_value_t> unwrap_to_vec(const hive_t& cont) {
        return unwrap_range(cont) | ranges::to<vector>();
    }

    static void try_forbid_alloc() {
        if constexpr (EH_al) {
            EH::forbid_alloc();
        }
    }
    static void try_allow_alloc() {
        if constexpr (EH_al) {
            EH::allow_alloc();
        }
    }

    template <class Pred>
    struct erase_proxy {
        Pred pred;
        raw_value_t val;

        // see [hive.erasure], equivalent to `elem == value` (not `value == elem`)
        bool operator==(const T&) const = delete;
        friend bool operator==(const T& elem, const erase_proxy& value) {
            return value.pred(elem, T{value.val});
        }
    };

public:
    static consteval bool static_test() {
        using X = hive_t;
        using A = Alloc;

#define TEST_DECL(declaration)        \
    {                                 \
        [[maybe_unused]] declaration; \
    }
#define ASSERT_RET(expr, ret, ...) \
    static_assert(requires {       \
        { expr }                   \
        __VA_ARGS__->same_as<ret>; \
    });                            \
    /*(void) (expr)*/ // TODO

        // [container.reqmts] and [container.rev.reqmts]
        (void) ([](X a, X b, const X c, const iter_t i, const iter_t j, const X& v, X& s, X& t, X&& rv) {
            // [container.reqmts]
            static_assert(is_same_v<typename X::value_type, T>);
            static_assert(is_same_v<typename X::reference, T&>);
            static_assert(is_same_v<typename X::const_reference, const T&>);

            static_assert(
                forward_iterator<iter_t> && is_same_v<iter_value_t<iter_t>, T> && convertible_to<iter_t, citer_t>);
            static_assert(forward_iterator<citer_t> && is_same_v<iter_value_t<citer_t>, T>);

            static_assert(signed_integral<diff_t> && is_same_v<diff_t, iter_difference_t<iter_t>>
                          && is_same_v<diff_t, iter_difference_t<citer_t>>);
            static_assert(unsigned_integral<size_ty> && sizeof(size_ty) >= sizeof(diff_t));

            if constexpr (has_default_al) {
                TEST_DECL(X u)
                TEST_DECL(X u = X())
            }
            if constexpr (Cpp17CopyInsertable) {
                TEST_DECL(X u(v))
                TEST_DECL(X u = v)
            }
            TEST_DECL(X u(move(rv)))
            TEST_DECL(X u = move(rv))

            if constexpr (Cpp17CopyInsertable && Cpp17CopyAssignable) {
                ASSERT_RET(a = t, X&);
            }
            if constexpr ((allocator_traits<A>::propagate_on_container_move_assignment::value
                              || allocator_traits<A>::is_always_equal::value)
                          || (Cpp17MoveInsertable && Cpp17MoveAssignable)) {
                ASSERT_RET(a = move(rv), X&);
            }

            ASSERT_RET(a.~X(), void);

            (void) ([&](const X cb) {
                ASSERT_RET(b.begin(), iter_t);
                ASSERT_RET(cb.begin(), citer_t);
                ASSERT_RET(b.end(), iter_t);
                ASSERT_RET(cb.end(), citer_t);

                ASSERT_RET(b.cbegin(), citer_t);
                ASSERT_RET(cb.cbegin(), citer_t);
                ASSERT_RET(b.cend(), citer_t);
                ASSERT_RET(cb.cend(), citer_t);
            });

            ASSERT_RET(i <=> j, strong_ordering); // hive supports it, though not random-access

            ASSERT_RET(t.swap(s), void);
            ASSERT_RET(swap(t, s), void);

            ASSERT_RET(c.size(), size_ty, noexcept);
            ASSERT_RET(c.max_size(), size_ty, noexcept);
            ASSERT_RET(c.empty(), bool, noexcept);

            (void) ([&](const citer_t ci, const citer_t cj) {
                constexpr auto test = [](const auto i, const auto j) {
                    static_assert(requires {
                        { i == j } -> boolean_testable;
                        { i != j } -> boolean_testable;
                        { i < j } -> boolean_testable;
                        { i <= j } -> boolean_testable;
                        { i >= j } -> boolean_testable;
                        { i > j } -> boolean_testable;
                        { i <=> j } -> same_as<strong_ordering>;
                    });
                };
                test(i, j);
                test(ci, j);
                test(i, cj);
                test(ci, cj);
            });

            // [container.rev.reqmts]
            static_assert(is_same_v<riter_t, reverse_iterator<iter_t>>);
            static_assert(is_same_v<criter_t, reverse_iterator<citer_t>>);

            (void) ([](X a, const X ca) {
                ASSERT_RET(a.rbegin(), riter_t, noexcept);
                ASSERT_RET(ca.rbegin(), criter_t, noexcept);
                ASSERT_RET(a.rend(), riter_t, noexcept);
                ASSERT_RET(ca.rend(), criter_t, noexcept);

                ASSERT_RET(a.crbegin(), criter_t, noexcept);
                ASSERT_RET(ca.crbegin(), criter_t, noexcept);
                ASSERT_RET(a.crend(), criter_t, noexcept);
                ASSERT_RET(ca.crend(), criter_t, noexcept);
            });
        });

        // [container.alloc.reqmts]
        (void) ([](const X& c, X& t, X&& rv, A m, hive_limits limits) {
            static_assert(is_same_v<typename X::allocator_type, A>);
            ASSERT_RET(c.get_allocator(), A, noexcept);

            TEST_DECL(X u(m))
            TEST_DECL(X u(limits, m)) // hive-specific
            if constexpr (Cpp17CopyInsertable) {
                TEST_DECL(X u(t, m))
            }
            if constexpr (Cpp17MoveInsertable) {
                TEST_DECL(X u(move(rv), m))
            }
        });

        // [sequence.reqmts]
        using another_rng_t    = custom_range<const T&, Alloc, input_iterator_tag, false, false, false>;
        using another_r_rng_t  = custom_range<T&& /**/, Alloc, input_iterator_tag, false, false, false>;
        using another_iter_t   = custom_range<const T&, Alloc, input_iterator_tag, true, false, false>::iterator;
        using another_r_iter_t = custom_range<T&& /**/, Alloc, input_iterator_tag, true, false, false>::iterator;
        (void) ([](X a, another_iter_t i, another_iter_t j, another_rng_t rg, initializer_list<T> il, size_ty n,
                    citer_t p, citer_t q, citer_t q1, citer_t q2, T& t, T&& rv, A m, hive_limits limits,
                    another_r_iter_t r_i, another_r_iter_t r_j, another_r_rng_t r_rg) {
            // hive-specific, see [hive.cons] and [hive.modifiers]
            if constexpr (Cpp17DefaultInsertable) {
                TEST_DECL(X u(n, m))
                TEST_DECL(X u(n, limits, m))
                if constexpr (has_default_al) {
                    TEST_DECL(X u(n))
                    TEST_DECL(X u(n, limits))
                }
            }
            if constexpr (Cpp17CopyInsertable) {
                TEST_DECL(X u(n, t, m))
                TEST_DECL(X u(n, t, limits, m))
                TEST_DECL(X u(i, j, m))
                TEST_DECL(X u(i, j, limits, m))
                TEST_DECL(X u(from_range, rg, m))
                TEST_DECL(X u(from_range, rg, limits, m))
                TEST_DECL(X u(il, m))
                TEST_DECL(X u(il, limits, m))
                if constexpr (has_default_al) {
                    TEST_DECL(X u(n, t))
                    TEST_DECL(X u(n, t, limits))
                    TEST_DECL(X u(i, j))
                    TEST_DECL(X u(i, j, limits))
                    TEST_DECL(X u(from_range, rg))
                    TEST_DECL(X u(from_range, rg, limits))
                    TEST_DECL(X u(il))
                    TEST_DECL(X u(il, limits))
                }
                if constexpr (Cpp17CopyAssignable) {
                    ASSERT_RET(a = il, X&);
                }
            }
            if constexpr (Cpp17MoveInsertable) {
                TEST_DECL(X u(r_i, r_j, m))
                TEST_DECL(X u(r_i, r_j, limits, m))
                TEST_DECL(X u(from_range, r_rg, m))
                TEST_DECL(X u(from_range, r_rg, limits, m))
                if constexpr (has_default_al) {
                    TEST_DECL(X u(r_i, r_j))
                    TEST_DECL(X u(r_i, r_j, limits))
                    TEST_DECL(X u(from_range, r_rg))
                    TEST_DECL(X u(from_range, r_rg, limits))
                }
            }

            if constexpr (Cpp17CopyInsertable) {
                ASSERT_RET(a.emplace(t), iter_t);
                ASSERT_RET(a.emplace_hint(p, t), iter_t);
                ASSERT_RET(a.insert(t), iter_t);
                ASSERT_RET(a.insert(p, t), iter_t);
                ASSERT_RET(a.insert(il), void);
                ASSERT_RET(a.insert_range(rg), void);
                ASSERT_RET(a.insert(n, t), void);
                ASSERT_RET(a.insert(i, j), void);
            }
            if constexpr (Cpp17MoveInsertable) {
                ASSERT_RET(a.emplace(move(rv)), iter_t);
                ASSERT_RET(a.emplace_hint(p, move(rv)), iter_t);
                ASSERT_RET(a.insert(move(rv)), iter_t);
                ASSERT_RET(a.insert(p, move(rv)), iter_t);
                ASSERT_RET(a.insert_range(r_rg), void);
                ASSERT_RET(a.insert(r_i, r_j), void);
            }
            // end hive-specific

            ASSERT_RET(a.erase(q), iter_t);
            ASSERT_RET(a.erase(q1, q2), iter_t);
            ASSERT_RET(a.clear(), void);

            if constexpr (Cpp17CopyInsertable && Cpp17CopyAssignable) {
                ASSERT_RET(a.assign(i, j), void);
                ASSERT_RET(a.assign_range(rg), void);
                ASSERT_RET(a.assign(il), void);
                ASSERT_RET(a.assign(n, t), void);
            }
            if constexpr (Cpp17MoveInsertable && Cpp17MoveAssignable) {
                ASSERT_RET(a.assign(r_i, r_j), void);
                ASSERT_RET(a.assign_range(r_rg), void);
            }
        });

        // [hive.operations]
        (void) ([](hive_t cont, hive_t another_cont, const hive_t const_cont, cptr_t ptr, EqualPred equal_pr,
                    LessPred less_pr) {
            ASSERT_RET(cont.splice(another_cont), void);
            ASSERT_RET(cont.splice(move(another_cont)), void);

            ASSERT_RET(cont.unique(equal_pr), size_ty);
            if constexpr (equality_comparable<T>) {
                ASSERT_RET(cont.unique(), size_ty);
            }

            if constexpr (Cpp17MoveInsertable && Cpp17MoveAssignable && Cpp17Swappable) {
                ASSERT_RET(cont.sort(less_pr), void);
                if constexpr (requires(const T& l, const T& r) {
                                  { l < r } -> boolean_testable;
                              }) {
                    ASSERT_RET(cont.sort(), void);
                }
            }

            ASSERT_RET(cont.get_iterator(ptr), iter_t, noexcept);
            ASSERT_RET(const_cont.get_iterator(ptr), citer_t, noexcept);
        });

        // [hive.erasure]
        (void) ([](hive_t cont, const T val, EqualPred equal_pr) {
            if constexpr (equality_comparable<T>) {
                ASSERT_RET(erase(cont, val), size_ty);
            }
            ASSERT_RET(erase(cont, erase_proxy{equal_pr, raw_value_t{}}), size_ty);
            ASSERT_RET(erase_if(cont, [](const T&) -> bool { abort(); }), size_ty);
        });

        // misc
        (void) ([](hive_t cont, const hive_t const_cont, size_ty n, hive_limits limits) {
            static_assert(bidirectional_iterator<iter_t>);
            static_assert(bidirectional_iterator<citer_t>);
            static_assert(bidirectional_iterator<riter_t>);
            static_assert(bidirectional_iterator<criter_t>);

            static_assert(three_way_comparable<iter_t, strong_ordering>);
            static_assert(three_way_comparable<citer_t, strong_ordering>);
            static_assert(three_way_comparable<riter_t, strong_ordering>);
            static_assert(three_way_comparable<criter_t, strong_ordering>);

            static_assert(!convertible_to<citer_t, iter_t>);
            static_assert(!convertible_to<citer_t*, iter_t*>);

            if constexpr (has_default_al) {
                static_assert(noexcept(hive_t()) >= noexcept(Alloc()));
            }
            static_assert(noexcept(hive_t(declval<const Alloc&>())));
            static_assert(noexcept(hive_t(declval<hive_t>())));
            if constexpr ((allocator_traits<Alloc>::propagate_on_container_move_assignment::value
                              || allocator_traits<Alloc>::is_always_equal::value)
                          || (Cpp17MoveInsertable && Cpp17MoveAssignable)) {
                static_assert(noexcept(cont = declval<hive_t>())
                              >= (allocator_traits<Alloc>::propagate_on_container_move_assignment::value
                                  || allocator_traits<Alloc>::is_always_equal::value));
            }
            static_assert(noexcept(cont.swap(cont)) >= (allocator_traits<Alloc>::propagate_on_container_swap::value
                                                        || allocator_traits<Alloc>::is_always_equal::value));
            static_assert(noexcept(swap(cont, cont)) >= noexcept(cont.swap(cont)));

            ASSERT_RET(const_cont.capacity(), size_ty, noexcept);
            ASSERT_RET(cont.reserve(n), void);
            if constexpr (Cpp17MoveInsertable) {
                ASSERT_RET(cont.shrink_to_fit(), void);
            }
            ASSERT_RET(cont.trim_capacity(), void, noexcept);
            ASSERT_RET(cont.trim_capacity(n), void, noexcept);
            ASSERT_RET(const_cont.block_capacity_limits(), hive_limits, noexcept);
            ASSERT_RET(hive_t::block_capacity_default_limits(), hive_limits, noexcept);
            ASSERT_RET(hive_t::block_capacity_hard_limits(), hive_limits, noexcept);
            if constexpr (Cpp17MoveInsertable) {
                ASSERT_RET(cont.reshape(limits), void);
            }
        });

#undef ASSERT_RET
#undef TEST_DECL

        // nonstandard test, _Is_hive_iterator
        {
            static_assert(_Is_hive_iterator<iter_t, true>);
            static_assert(_Is_hive_iterator<iter_t>);
            static_assert(_Is_hive_iterator<citer_t>);
            static_assert(!_Is_hive_iterator<citer_t, true>);

            static_assert(_Is_hive_riterator<riter_t, true>);
            static_assert(_Is_hive_riterator<riter_t>);
            static_assert(_Is_hive_riterator<criter_t>);
            static_assert(!_Is_hive_riterator<criter_t, true>);

            struct evil_iter : iter_t {};
            static_assert(!_Is_hive_iterator<evil_iter>);
            static_assert(!_Is_hive_riterator<evil_iter>);
            static_assert(!_Is_hive_riterator<reverse_iterator<evil_iter>>);
        }

        return true;
    }

    constexpr void test_limits() {
        // [hive.overview]/5
        const auto hard_limits    = hive_t::block_capacity_hard_limits();
        const auto default_limits = hive_t::block_capacity_default_limits();
        assert(hard_limits.min <= default_limits.min);
        assert(default_limits.min <= default_limits.max);
        assert(default_limits.max <= hard_limits.max);
        if constexpr (has_default_al
                      || !requires(const Alloc& al) { al.max_size(); }) { // FIXME: see `block_capacity_hard_limits()`
            assert(hard_limits.max <= allocator_traits<Alloc>::max_size(al_1));
            assert(hard_limits.max <= allocator_traits<Alloc>::max_size(al_2));
        }
    }

private:
    template <bool Move, class Fn>
    void range_matrix(Fn func, Alloc& al, size_ty cnt) {
        using reference = conditional_t<Move, T&&, const T&>;

        auto src_rng = gen_raw_rng(cnt);
        if constexpr (!Move) {
            // contiguous common range
            using ctg_range = custom_range<T&, Alloc, contiguous_iterator_tag, true, true, true>;
            static_assert(ranges::contiguous_range<ctg_range>);
            static_assert(ranges::sized_range<ctg_range>);
            static_assert(ranges::common_range<ctg_range>);

            ctg_range rng(from_range, src_rng, al);
            func([&] -> auto& { return rng; });
        } else {
            // random-access common range
            using rnd_range = custom_range<reference, Alloc, random_access_iterator_tag, true, true, true>;
            static_assert(ranges::random_access_range<rnd_range>);
            static_assert(ranges::sized_range<rnd_range>);
            static_assert(ranges::common_range<rnd_range>);

            rnd_range rng(from_range, src_rng, al);
            func([&] -> auto& { return rng; });
        }
        {
            // unsized common forward range
            using fwd_range = custom_range<reference, Alloc, forward_iterator_tag, true, false, false>;
            static_assert(ranges::forward_range<fwd_range>);
            static_assert(!ranges::bidirectional_range<fwd_range>);
            static_assert(!ranges::sized_range<fwd_range>);
            static_assert(ranges::common_range<fwd_range>);
            using range_it = fwd_range::iterator;
            static_assert(!sized_sentinel_for<range_it, range_it>);

            fwd_range rng(from_range, src_rng, al);
            func([&] -> auto& { return rng; });
        }
        {
            // sized uncommon input range, with unsized sentinel
            using in_range = custom_range<reference, Alloc, input_iterator_tag, false, true, false>;
            static_assert(ranges::input_range<in_range>);
            static_assert(!ranges::forward_range<in_range>);
            static_assert(ranges::sized_range<in_range>);
            static_assert(!ranges::common_range<in_range>);
            using range_it = in_range::iterator;
            using range_se = decltype(ranges::end(declval<in_range&>()));
            static_assert(!sized_sentinel_for<range_se, range_it>);

            func([&] { return in_range(from_range, src_rng, al); });
        }
    }

    template <class Fn>
    static void ctor_matrix(Fn func, Alloc& al, hive_limits limits) {
        const auto default_limits = hive_t::block_capacity_default_limits();
        if constexpr (has_default_al) {
            func(Alloc(), default_limits);
            func(Alloc(), limits, limits);
        }
        func(al, default_limits, al);
        func(al, limits, limits, al);
    }

    static void ctor_constexpr()
        requires is_same_v<Alloc, allocator<T>>
    {
        [[maybe_unused]] constexpr auto default_limits = hive_t::block_capacity_default_limits();
        [[maybe_unused]] constexpr auto hard_limits    = hive_t::block_capacity_hard_limits();
#pragma warning(push)
#pragma warning(disable : 4640) // construction of local static object is not thread-safe
#ifndef __EDG__ // TRANSITION, DevCom-11049681
        static constinit hive_t m_hive1;
        static constinit hive_t m_hive2(allocator<T>{});
        static constinit hive_t m_hive3(default_limits);
        static constinit hive_t m_hive4(hard_limits, allocator<T>{});
#endif // !defined(__EDG__)
#pragma warning(pop)
    }

public:
    void test_ctors() {
        DO_IF_VALID(ctor_constexpr());

        for (const auto& [limits, counts] : limits_counts_mat) {
            // default ctor
            ctor_matrix(
                [](const Alloc& expected_al, hive_limits expected_limits, auto&&... args) {
                    hive_t cont(args...);
                    assert(cont.get_allocator() == expected_al);
                    assert_limits(cont, expected_limits);
                    assert(cont.empty());
                },
                al_1, limits);

            for (const auto& cnt : counts) {
                // default fill ctor
                if constexpr (Cpp17DefaultInsertable) {
                    const T default_val = [] {
                        if constexpr (tagged_al) {
                            return T{tag_t{}};
                        } else {
                            return T{};
                        }
                    }();
                    ctor_matrix(
                        [&](const Alloc& expected_al, hive_limits expected_limits, auto&&... args) {
                            hive_t cont(cnt, args...);
                            assert(cont.get_allocator() == expected_al);
                            assert_limits(cont, expected_limits);
                            assert(ranges::all_of(cont, [&](const T& val) { return equal_pred(val, default_val); }));
                            assert(cont.size() == cnt);
                        },
                        al_1, limits);
                }

                // fill ctor
                if constexpr (Cpp17CopyInsertable) {
                    ctor_matrix(
                        [&](const Alloc& expected_al, hive_limits expected_limits, auto&&... args) {
                            const T val{gen_raw_value()};
                            hive_t cont(cnt, val, args...);
                            assert(cont.get_allocator() == expected_al);
                            assert_limits(cont, expected_limits);
                            assert(ranges::all_of(cont, [&](const T& v) { return equal_pred(v, val); }));
                            assert(cont.size() == cnt);
                        },
                        al_1, limits);
                }

                // range ctor
                {
                    const auto matrix = [&](auto get_rng) {
                        if constexpr (ranges::common_range<decltype(get_rng())>) {
                            ctor_matrix(
                                [&](const Alloc& expected_al, hive_limits expected_limits, auto&&... args) {
                                    auto&& rg = get_rng();
                                    hive_t cont(ranges::begin(rg), ranges::end(rg), args...);
                                    assert(cont.get_allocator() == expected_al);
                                    assert_limits(cont, expected_limits);
                                    assert_equal(cont, get_rng());
                                },
                                al_1, limits);
                        }

                        ctor_matrix(
                            [&](const Alloc& expected_al, hive_limits expected_limits, auto&&... args) {
                                hive_t cont(from_range, get_rng(), args...);
                                assert(cont.get_allocator() == expected_al);
                                assert_limits(cont, expected_limits);
                                assert_equal(cont, get_rng());
                            },
                            al_1, limits);
                    };

                    if constexpr (Cpp17CopyInsertable) {
                        range_matrix<false>(matrix, al_1, cnt);
                    }
                    if constexpr (Cpp17MoveInsertable) {
                        range_matrix<true>(matrix, al_1, cnt);
                    }

                    if constexpr (!is_same_v<raw_value_t, T>) {
                        auto raw_rng = gen_raw_rng(cnt);
                        matrix([&] -> auto& { return raw_rng; });
                    }
                }

                // copy ctor
                if constexpr (Cpp17CopyInsertable) {
                    auto test = [&](const Alloc& expected_al, auto&&... args) {
                        hive_matrix(
                            [&](const hive_t& src) {
                                const auto src_vals = unwrap_to_vec(src);
                                hive_t dst(src, args...);
                                assert(dst.get_allocator() == expected_al);
                                assert_limits(dst, limits);
                                assert_equal(dst, src_vals);

                                assert(src.get_allocator() == al_1);
                                assert_limits(src, limits);
                                assert_equal(src, src_vals);
                            },
                            al_1, limits, cnt);
                    };
                    test(al_traits::select_on_container_copy_construction(al_1));
                    test(al_2, al_2);
                }

                // move ctor
                {
                    auto test = [&](const Alloc& expected_al, auto&&... args) {
                        hive_matrix(
                            [&](hive_t& src) {
                                const bool fast_move = src.get_allocator() == expected_al;

                                const auto src_vals  = unwrap_to_vec(src);
                                const auto src_begin = src.begin();

                                if (fast_move) {
                                    try_forbid_alloc();
                                }
                                hive_t dst(move(src), args...);
                                if (fast_move) {
                                    try_allow_alloc();
                                    if (!dst.empty()) {
                                        assert(src_begin == dst.begin());
                                    }
                                }

                                assert(dst.get_allocator() == expected_al);
                                assert_limits(dst, limits);
                                assert_equal(dst, src_vals);

                                assert(src.empty());
                            },
                            al_1, limits, cnt);
                    };
                    test(al_1);
                    if constexpr (!different_al || Cpp17MoveInsertable) {
                        test(al_2, al_2);
                    }
                }
            }
        }
    }

private:
    template <class Fn>
    void hive_fn_matrix(Fn func, Alloc& al, hive_limits limits, size_ty cnt_hint) {
        // all these functions return a unique_ptr to ensure no hive move constructor is called
        bool need_completely_full_test = true;
        func([&] {
            // full hive
            auto cont                 = make_unique<hive_t>(from_range, gen_raw_rng(cnt_hint), limits, al);
            need_completely_full_test = cont->size() != cont->capacity();
            return cont;
        });
        if (need_completely_full_test) {
            func([&] {
                // completely full hive
                auto cont      = make_unique<hive_t>(from_range, gen_raw_rng(cnt_hint), limits, al);
                const auto siz = cont->size();
                const auto cap = cont->capacity();
                cont->insert_range(gen_raw_rng(cap - siz));
                assert(cont->size() == cont->capacity());
                return cont;
            });
        }
        func([&] {
            // hive with erased elements
            auto cont             = make_unique<hive_t>(from_range, gen_raw_rng(cnt_hint * 2), limits, al);
            vector<citer_t> iters = get_hive_nonend_iters(*cont);
            ranges::shuffle(iters, rand_engine);
            iters.resize(cnt_hint);
            for (const auto& iter : iters) {
                cont->erase(iter);
            }
            assert(cont->size() == cnt_hint);
            return cont;
        });
        func([&] {
            // hive with reserved blocks
            auto cont      = make_unique<hive_t>(from_range, gen_raw_rng(cnt_hint), limits, al);
            const auto cap = cont->capacity();
            const auto siz = cont->size();
            cont->reserve(static_cast<size_ty>(cap + siz));
            assert(cont->capacity() >= cap + siz);
            return cont;
        });
    }
    template <class Fn>
    void hive_matrix(Fn func, Alloc& al, hive_limits limits, size_ty cnt_hint) {
        hive_fn_matrix([&](auto&& get_cont) { func(*get_cont()); }, al, limits, cnt_hint);
    }

    template <class Fn>
    void hive_matrix_2(Fn func, Alloc& alloc_1, Alloc& alloc_2, hive_limits limits_1, hive_limits limits_2,
        size_ty cnth_1, size_ty cnth_2) {
        hive_fn_matrix(
            [&](auto&& get_hive_1) {
                hive_fn_matrix(
                    [&](auto&& get_hive_2) { func(*get_hive_1(), *get_hive_2()); }, alloc_2, limits_2, cnth_2);
            },
            alloc_1, limits_1, cnth_1);
    }

    template <class Fn, class Matrix>
    void hive_matrix(Fn func, Alloc& al, const Matrix& matrix) {
        for (const auto& [limits, counts] : matrix) {
            for (const auto& cnt : counts) {
                hive_matrix(func, al, limits, cnt);
            }
        }
    }
    template <class Fn, class Matrix>
    void hive_matrix_2(Fn func, Alloc& alloc_1, Alloc& alloc_2, const Matrix& matrix) {
        for (const auto& [limits_1, counts_1] : matrix) {
            for (const auto& cnt_1 : counts_1) {
                for (const auto& [limits_2, counts_2] : matrix) {
                    for (const auto& cnt_2 : counts_2) {
                        hive_matrix_2(func, alloc_1, alloc_2, limits_1, limits_2, cnt_1, cnt_2);
                    }
                }
            }
        }
    }

public:
    void test_assign() {
        for (const auto& [limits, counts] : limits_counts_mat) {
            for (const auto& old_cnt : counts) {
                // ilist assign
                if constexpr (Cpp17CopyInsertable && Cpp17CopyAssignable) {
                    hive_matrix(
                        [&](hive_t& cont) {
                            const auto raw_vec = gen_raw_rng(5) | ranges::to<vector>();
                            cont.assign({T{raw_vec[0]}, T{raw_vec[1]}, T{raw_vec[2]}, T{raw_vec[3]}, T{raw_vec[4]}});
                            assert_equal(cont, raw_vec);
                        },
                        al_1, limits, old_cnt);
                }

                for (const auto& new_cnt : counts) {
                    // fill assign
                    if constexpr (Cpp17CopyInsertable && Cpp17CopyAssignable) {
                        hive_matrix(
                            [&](hive_t& cont) {
                                const T val{gen_raw_value()};
                                cont.assign(new_cnt, val);
                                assert(ranges::all_of(cont, [&](const T& v) { return equal_pred(v, val); }));
                                assert(cont.size() == new_cnt);
                            },
                            al_1, limits, old_cnt);
                    }

                    // range assign
                    {
                        const auto matrix = [&](auto get_rng) {
                            if constexpr (ranges::common_range<decltype(get_rng())>) {
                                hive_matrix(
                                    [&](hive_t& cont) {
                                        auto&& rg = get_rng();
                                        cont.assign(ranges::begin(rg), ranges::end(rg));
                                        assert_equal(cont, get_rng());
                                    },
                                    al_1, limits, old_cnt);
                            }

                            hive_matrix(
                                [&](hive_t& cont) {
                                    cont.assign_range(get_rng());
                                    assert_equal(cont, get_rng());
                                },
                                al_1, limits, old_cnt);
                        };

                        if constexpr (Cpp17CopyInsertable && Cpp17CopyAssignable) {
                            range_matrix<false>(matrix, al_1, new_cnt);

                            // fake overlap
                            hive_matrix(
                                [&](hive_t& dst) {
                                    dst.assign_range(ranges::subrange{dst.begin(), dst.begin()});
                                    dst.assign_range(ranges::subrange{dst.rbegin(), dst.rbegin()});
                                    dst.assign(dst.begin(), dst.begin());
                                    dst.assign(dst.rbegin(), dst.rbegin());
                                    dst.assign_range(dst);
                                    assert(dst.empty());
                                },
                                al_1, limits, old_cnt);
                        }
                        if constexpr (Cpp17MoveInsertable && Cpp17MoveAssignable) {
                            range_matrix<true>(matrix, al_1, new_cnt);
                        }

                        if constexpr (!is_same_v<raw_value_t, T> && assignable_from<T&, raw_value_t>) {
                            auto raw_rng = gen_raw_rng(new_cnt);
                            matrix([&] -> auto& { return raw_rng; });
                        }
                    }
                }
            }
        }

        // copy assign
        static constexpr bool pocca = al_traits::propagate_on_container_copy_assignment::value;
        if constexpr (Cpp17CopyInsertable && Cpp17CopyAssignable) {
            const auto test = [&](hive_t& left, const hive_t& right) {
                const auto l_al  = left.get_allocator();
                const auto l_lim = left.block_capacity_limits();
                const auto r_al  = right.get_allocator();
                const auto r_val = unwrap_to_vec(right);
                const auto r_lim = right.block_capacity_limits();

                left = right;

                assert_equal(left, r_val);
                assert_equal(right, r_val);
                assert_limits(left, l_lim);
                assert_limits(right, r_lim);
                if constexpr (pocca) {
                    assert(left.get_allocator() == r_al);
                } else {
                    assert(left.get_allocator() == l_al);
                }
                assert(right.get_allocator() == r_al);
            };

            hive_matrix_2(test, al_1, al_1, limits_counts_mat_reduced);
            if constexpr (different_al) {
                hive_matrix_2(test, al_1, al_2, limits_counts_mat_reduced);
            }
        }

        // move assign
        static constexpr bool pocma = al_traits::propagate_on_container_move_assignment::value;
        if constexpr ((pocma || !different_al) || (Cpp17MoveInsertable && Cpp17MoveAssignable)) {
            const auto test = [&](hive_t& left, hive_t& right) {
                const bool fast_move = pocma || left.get_allocator() == right.get_allocator();

                const auto l_al    = left.get_allocator();
                const auto l_lim   = left.block_capacity_limits();
                const auto r_al    = right.get_allocator();
                const auto r_val   = unwrap_to_vec(right);
                const auto r_lim   = right.block_capacity_limits();
                const auto r_begin = right.begin();

                if (fast_move) {
                    try_forbid_alloc();
                }
                left = move(right);
                if (fast_move) {
                    try_allow_alloc();
                    if (!left.empty()) {
                        assert(r_begin == left.begin());
                    }
                }

                assert_equal(left, r_val);
                if (fast_move) {
                    assert_limits(left, r_lim);
                } else {
                    assert_limits(left, l_lim);
                }
                if constexpr (pocma) {
                    assert(left.get_allocator() == r_al);
                } else {
                    assert(left.get_allocator() == l_al);
                }

                assert(right.empty());
            };

            hive_matrix_2(test, al_1, al_2, limits_counts_mat_reduced);
            if constexpr (different_al) {
                hive_matrix_2(test, al_2, al_1, limits_counts_mat_reduced);
            }
        }
    }

    void test_reserve() {
        hive_matrix(
            [&](hive_t& cont) {
                const auto old_begin = cont.begin();
                const auto vals      = unwrap_to_vec(cont);
                const auto old_cap   = cont.capacity();

                try_forbid_alloc();
                cont.reserve(old_cap);
                try_allow_alloc();
                assert(cont.capacity() == old_cap);
                assert(old_begin == cont.begin());
                assert_equal(cont, vals);
                try_forbid_alloc();
                cont.reserve(0);
                try_allow_alloc();
                assert(cont.capacity() == old_cap);
                assert(old_begin == cont.begin());
                assert_equal(cont, vals);

                cont.reserve(static_cast<size_ty>(old_cap + 1));
                assert(cont.capacity() >= old_cap + 1uz);
                assert(old_begin == cont.begin());
                assert_equal(cont, vals);

                // > max_size()
                if (cont.max_size() < numeric_limits<size_ty>::max()) {
                    assert_throw<length_error>([&] { cont.reserve(static_cast<size_ty>(cont.max_size() + 1)); });
                }
            },
            al_1, limits_counts_mat);
    }

    void test_shrink_to_fit()
        requires Cpp17MoveInsertable
    {
        hive_matrix(
            [&](hive_t& cont) {
                const auto vals      = unwrap_to_vec(cont);
                const auto old_cap   = cont.capacity();
                const bool no_effect = old_cap == cont.size();

                if (no_effect) {
                    try_forbid_alloc();
                }
                cont.shrink_to_fit();
                if (no_effect) {
                    try_allow_alloc();
                }

                if (no_effect) {
                    assert_equal(cont, vals);
                } else {
                    assert_permutation(cont, vals);

                    const auto limits          = cont.block_capacity_limits();
                    const auto min_block_count = (cont.size() + (limits.max - 1)) / limits.max;
                    const auto min_capacity    = max(static_cast<size_ty>(min_block_count * limits.min), cont.size());
                    assert(cont.capacity() == min_capacity); // NB: nonstandard guarantee
                }
                assert(cont.capacity() <= old_cap);
            },
            al_1, limits_counts_mat);
    }

    void test_trim_capacity() {
        hive_matrix(
            [&](hive_t& cont) {
                const auto vals = unwrap_to_vec(cont);
                auto old_cap    = cont.capacity();
                try_forbid_alloc();
                cont.trim_capacity();
                try_allow_alloc();
                assert(cont.capacity() <= old_cap);
                assert_equal(cont, vals);

                old_cap = cont.capacity();
                cont.reserve(static_cast<size_ty>(old_cap + 1));
                try_forbid_alloc();
                cont.trim_capacity();
                try_allow_alloc();
                assert(cont.capacity() == old_cap);
                assert_equal(cont, vals);
            },
            al_1, limits_counts_mat);

        hive_matrix(
            [&](hive_t& cont) {
                const auto vals    = unwrap_to_vec(cont);
                const auto old_cap = cont.capacity();
                try_forbid_alloc();
                cont.trim_capacity(old_cap);
                try_allow_alloc();
                assert(cont.capacity() == old_cap);
                assert_equal(cont, vals);

                try_forbid_alloc();
                cont.trim_capacity(static_cast<size_ty>(old_cap + 1));
                try_allow_alloc();
                assert(cont.capacity() == old_cap);
                assert_equal(cont, vals);

                const auto cont_size = cont.size();
                cont.reserve(min(cont.max_size(), static_cast<size_ty>(cont.capacity() + 1)));
                cont.reserve(min(cont.max_size(), static_cast<size_ty>(cont.capacity() + 1)));
                try_forbid_alloc();
                cont.trim_capacity(static_cast<size_ty>(cont_size + 1));
                try_allow_alloc();
                assert(cont.capacity() >= cont_size + 1uz);
                assert_equal(cont, vals);
            },
            al_1, limits_counts_mat);
    }

    void test_reshape()
        requires Cpp17MoveInsertable
    {
        for (const auto& [old_limits, counts] : limits_counts_mat) {
            for (const auto& cnt : counts) {
                for (const auto& [new_limits, _] : limits_counts_mat) {
                    hive_matrix(
                        [&](hive_t& cont) {
                            const auto vals      = unwrap_to_vec(cont);
                            const bool all_fit   = new_limits.min <= old_limits.min && old_limits.max <= new_limits.max;
                            const auto old_begin = cont.begin();

                            if (all_fit) {
                                try_forbid_alloc();
                            }
                            cont.reshape(new_limits);
                            if (all_fit) {
                                try_allow_alloc();
                                assert(old_begin == cont.begin());
                            }

                            if (all_fit) {
                                assert_equal(cont, vals);
                            } else {
                                assert_permutation(cont, vals);
                            }
                            assert_limits(cont, new_limits);
                        },
                        al_1, old_limits, cnt);
                }
            }
        }
    }

    void test_insert() {
        for (const auto& [limits, counts] : limits_counts_mat) {
            for (const auto& cnt : counts) {
                // skip functions like emplace_hint since they are too trivial

                // emplace
                hive_matrix(
                    [&](hive_t& cont) {
                        auto expect = unwrap_to_vec(cont);
                        expect.reserve(expect.capacity() + cnt);

                        for (auto&& raw_val : gen_raw_rng(cnt)) {
                            assert(equal_pred(*cont.emplace(raw_val), T{raw_val}));
                            expect.emplace_back(raw_val);
                        }

                        assert_permutation(cont, expect);
                    },
                    al_1, limits, cnt);

                if constexpr (Cpp17CopyInsertable) {
                    // fill insert
                    hive_matrix(
                        [&](hive_t& cont) {
                            auto expect = unwrap_to_vec(cont);

                            const auto raw_val = gen_raw_value();
                            const T val{raw_val};
                            cont.insert(cnt, val);

                            expect.insert(expect.end(), cnt, raw_val);
                            assert_permutation(cont, expect);
                        },
                        al_1, limits, cnt);

                    // ilist insert
                    hive_matrix(
                        [&](hive_t& cont) {
                            auto expect = unwrap_to_vec(cont);

                            const auto raw_vec = gen_raw_rng(5) | ranges::to<vector>();
                            cont.insert({T{raw_vec[0]}, T{raw_vec[1]}, T{raw_vec[2]}, T{raw_vec[3]}, T{raw_vec[4]}});

                            expect.insert_range(expect.end(), raw_vec);
                            assert_permutation(cont, expect);
                        },
                        al_1, limits, cnt);
                }

                // range insert
                {
                    const auto matrix = [&](auto get_rng) {
                        if constexpr (ranges::common_range<decltype(get_rng())>) {
                            hive_matrix(
                                [&](hive_t& dst) {
                                    auto expect = unwrap_to_vec(dst);

                                    auto&& rg = get_rng();
                                    dst.insert(ranges::begin(rg), ranges::end(rg));

                                    expect.insert_range(expect.end(), unwrap_range(get_rng()));
                                    assert_permutation(dst, expect);
                                },
                                al_1, limits, cnt);
                        }

                        hive_matrix(
                            [&](hive_t& dst) {
                                auto expect = unwrap_to_vec(dst);

                                auto&& rg = get_rng();
                                dst.insert_range(rg);

                                expect.insert_range(expect.end(), unwrap_range(get_rng()));
                                assert_permutation(dst, expect);
                            },
                            al_1, limits, cnt);
                    };

                    if constexpr (Cpp17CopyInsertable) {
                        range_matrix<false>(matrix, al_1, cnt);

                        // fake overlap
                        hive_matrix(
                            [&](hive_t& dst) {
                                const auto expect = unwrap_to_vec(dst);

                                if (dst.empty()) {
                                    dst.insert_range(dst);
                                }
                                dst.insert_range(ranges::subrange{dst.begin(), dst.begin()});
                                dst.insert_range(ranges::subrange{dst.rbegin(), dst.rbegin()});
                                dst.insert(dst.begin(), dst.begin());
                                dst.insert(dst.rbegin(), dst.rbegin());

                                assert_equal(dst, expect);
                            },
                            al_1, limits, cnt);
                    }
                    if constexpr (Cpp17MoveInsertable) {
                        range_matrix<true>(matrix, al_1, cnt);
                    }

                    if constexpr (!is_same_v<raw_value_t, T>) {
                        auto raw_rng = gen_raw_rng(cnt);
                        matrix([&] -> auto& { return raw_rng; });
                    }
                }
            }
        }
    }

    void test_erase() {
        hive_matrix(
            [&](hive_t& cont) {
                auto remaining = cont.size();
                while (!cont.empty()) {
                    cont.erase(cont.begin());
                    --remaining;
                }
                assert(remaining == 0);
            },
            al_1, limits_counts_mat);

        hive_matrix(
            [&](hive_t& cont) {
                const size_t init_size = cont.size();

                using hive_iter = iter_t;
                using list_iter = list<raw_value_t>::iterator;
                using iter_pair = pair<hive_iter, list_iter>;
                auto vals       = unwrap_range(cont) | ranges::to<list>();
                vector<iter_pair> iters(init_size);
                {
                    auto hive_it = cont.begin();
                    auto list_it = vals.begin();
                    for (size_t i = 0; i != cont.size(); ++i) {
                        iters[i] = {hive_it, list_it};
                        ++hive_it, ++list_it;
                    }
                }

                ranges::shuffle(iters, rand_engine);

                size_t index = 0;
                for (; index != init_size / 3; ++index) {
                    cont.erase(iters[index].first);
                    vals.erase(iters[index].second);
                }
                assert_equal(cont, vals);
                for (; index != init_size * 3 / 4; ++index) {
                    cont.erase(iters[index].first);
                    vals.erase(iters[index].second);
                }
                assert_equal(cont, vals);
            },
            al_1, limits_counts_mat);

        hive_matrix(
            [&](hive_t& cont) {
                if (cont.empty()) {
                    cont.erase(cont.end(), cont.end());
                    assert(cont.empty());
                    return;
                }

                auto vals = unwrap_to_vec(cont);

                array<ptrdiff_t, 2> offsets;
                ranges::sample(views::iota(0, ssize(cont) + 1), offsets.data(), 2, rand_engine);
                assert(offsets[0] < offsets[1]); // sample is stable here

                cont.erase(next(cont.begin(), static_cast<diff_t>(offsets[0])),
                    next(cont.begin(), static_cast<diff_t>(offsets[1])));

                vals.erase(vals.begin() + offsets[0], vals.begin() + offsets[1]);
                assert_equal(cont, vals);
            },
            al_1, limits_counts_mat);

        hive_matrix(
            [&](hive_t& cont) {
                cont.clear();
                assert(cont.empty());
            },
            al_1, limits_counts_mat);

        hive_matrix(
            [&](hive_t& cont) {
                counted_pred pred{equal_pred};
                if (cont.empty()) {
                    const auto ret = erase(cont, erase_proxy{ref(pred), raw_value_t{}});
                    assert(pred.cnt == 0);
                    assert(cont.empty());
                    assert(ret == 0);
                    return;
                }

                const auto size_before = cont.size();
                auto expect            = unwrap_to_vec(cont);
                const auto ret         = erase(cont, erase_proxy{ref(pred), expect[0]});
                assert(pred.cnt == size_before);
                assert(ret == size_before - cont.size());

                erase(expect, raw_value_t{expect[0]}); // must copy because `erase` takes its argument by reference
                assert_equal(cont, expect);
            },
            al_1, limits_counts_mat);

        hive_matrix(
            [&](hive_t& cont) {
                if (cont.empty()) {
                    const auto ret = erase_if(cont, [](const T&) -> bool { abort(); });
                    assert(cont.empty());
                    assert(ret == 0);
                    return;
                }

                const auto size_before = cont.size();
                auto expect            = unwrap_to_vec(cont);
                counted_pred pred_cont{[&](const T& v) { return less_pred(v, T{expect[0]}); }};
                const auto ret = erase_if(cont, ref(pred_cont));
                assert(pred_cont.cnt == size_before);
                assert(ret == size_before - cont.size());

                erase_if(expect, [val = expect[0]](const raw_value_t& v) { return v < val; });
                assert_equal(cont, expect);
            },
            al_1, limits_counts_mat);
    }

    void test_swap() {
        const auto test = [&](Alloc& l_al, Alloc& r_al, auto&& func) {
            hive_matrix_2(
                [&](hive_t& left, hive_t& right) {
                    const auto l_val = unwrap_to_vec(left);
                    const auto l_cap = left.capacity();
                    const auto l_lim = left.block_capacity_limits();
                    const auto r_val = unwrap_to_vec(right);
                    const auto r_cap = right.capacity();
                    const auto r_lim = right.block_capacity_limits();

                    try_forbid_alloc();
                    func(left, right);
                    try_allow_alloc();

                    assert_equal(left, r_val);
                    assert_equal(right, l_val);
                    assert(left.capacity() == r_cap);
                    assert(right.capacity() == l_cap);
                    assert_limits(left, r_lim);
                    assert_limits(right, l_lim);
                    if constexpr (al_traits::propagate_on_container_swap::value) {
                        assert(left.get_allocator() == r_al);
                        assert(right.get_allocator() == l_al);
                    }
                },
                l_al, r_al, limits_counts_mat_reduced);
        };
        test(al_1, al_1, [](hive_t& left, hive_t& right) { left.swap(right); });
        test(al_1, al_1, [](hive_t& left, hive_t& right) { swap(left, right); });
        if constexpr (different_al && al_traits::propagate_on_container_swap::value) {
            test(al_1, al_2, [](hive_t& left, hive_t& right) { left.swap(right); });
            test(al_1, al_2, [](hive_t& left, hive_t& right) { swap(left, right); });
        }
    }

private:
    struct strong_guarantee_state {
        vector<raw_value_t> unwrapped_values;
        vector<citer_t> nonend_iters;
        citer_t end_iter;
        size_ty capacity;
        hive_limits limits;
        Alloc al;

        explicit strong_guarantee_state(const hive_t& cont)
            : unwrapped_values(unwrap_to_vec(cont)), nonend_iters(get_hive_nonend_iters(cont)), end_iter(cont.end()),
              capacity(cont.capacity()), limits(cont.block_capacity_limits()), al(cont.get_allocator()) {}

        void assert_eq(const hive_t& cont) const noexcept {
            assert(unwrap_to_vec(cont) == unwrapped_values);

            auto it = cont.begin();
            for (size_t i = 0; i != nonend_iters.size(); ++i) {
                assert(nonend_iters[i] == it);
                ++it;
            }
            assert(it == cont.end());
            assert(end_iter == cont.end());

            assert(cont.capacity() == capacity);

            assert_limits(cont, limits);

            assert(cont.get_allocator() == al);
        }
    };

    void splice_nothrow(hive_t& src, hive_t& dst) noexcept {
        auto expect = unwrap_to_vec(src);
        expect.insert_range(expect.end(), unwrap_range(dst));
        const auto cap_sum = src.capacity() + dst.capacity();

        try_forbid_alloc();
        dst.splice(src);
        try_allow_alloc();

        assert(src.empty());
        assert_permutation(dst, expect);
        assert(src.capacity() + dst.capacity() == cap_sum);
    }
    void splice_throw(hive_t& src, hive_t& dst) noexcept {
        strong_guarantee_state src_state{src};
        strong_guarantee_state dst_state{dst};

        try_forbid_alloc();
        assert_throw<length_error>([&] { dst.splice(src); });
        try_allow_alloc();

        src_state.assert_eq(src);
        dst_state.assert_eq(dst);
    }

public:
    void test_splice() {
        for (const auto& [src_limits, src_counts] : limits_counts_mat_reduced) {
            for (const auto& src_cnt : src_counts) {
                for (const auto& [dst_limits, dst_counts] : limits_counts_mat_reduced) {
                    for (const auto& dst_cnt : dst_counts) {
                        if (dst_limits.max >= src_limits.max && src_limits.min >= dst_limits.min) {
                            // completely contains
                            hive_matrix_2([&](hive_t& src, hive_t& dst) { splice_nothrow(src, dst); }, al_1, al_1,
                                src_limits, dst_limits, src_cnt, dst_cnt);
                        } else if (src_limits.max >= dst_limits.min && dst_limits.max >= src_limits.min) {
                            // has overlap
                            if constexpr (Cpp17MoveInsertable) { // can reshape
                                const size_t common_size =
                                    src_limits.min >= dst_limits.min ? src_limits.min : dst_limits.min;
                                assert(src_limits.min <= common_size);
                                assert(common_size <= src_limits.max);
                                assert(dst_limits.min <= common_size);
                                assert(common_size <= dst_limits.max);
                                const hive_limits common_limits{common_size, common_size};

                                hive_matrix_2(
                                    [&](hive_t& src, hive_t& dst) {
                                        src.reshape(src_limits);
                                        splice_nothrow(src, dst);
                                    },
                                    al_1, al_1, common_limits, dst_limits, src_cnt, dst_cnt);
                            }
                        } else {
                            // no overlap
                            hive_matrix_2(
                                [&](hive_t& src, hive_t& dst) {
                                    if (!src.empty()) {
                                        splice_throw(src, dst);
                                    } else {
                                        splice_nothrow(src, dst);
                                    }
                                },
                                al_1, al_1, src_limits, dst_limits, src_cnt, dst_cnt);
                        }
                    }
                }
            }
        }

        // > max_size()
        if constexpr (small_al) {
            hive_t src(al_1);
            hive_t dst(al_1);
            const auto max_size = dst.max_size();
            assert(max_size >= 2);

            src.insert_range(gen_raw_rng(max_size / 2 + 1));
            dst.insert_range(gen_raw_rng(max_size / 2 + 1));

            splice_throw(src, dst); // nonstandard test, _Xlength()
        }
    }

    void test_unique() {
        hive_matrix(
            [&](hive_t& cont) {
                cont.insert_range(views::repeat(gen_raw_value(), 3));
                cont.insert_range(views::repeat(gen_raw_value(), 4));
                cont.insert_range(views::repeat(gen_raw_value(), 2));
                const auto size_before = cont.size();
                auto expect            = unwrap_to_vec(cont);
                expect.erase(ranges::unique(expect).begin(), expect.end());
                const auto expected_ret = cont.size() - expect.size();

                counted_pred pred{equal_pred};
                const auto ret = cont.unique(ref(pred));
                assert(pred.cnt == size_before - 1uz);
                assert(ret == expected_ret);
                assert_equal(cont, expect);
            },
            al_1, limits_counts_mat);
    }

    void test_sort()
        requires (Cpp17MoveInsertable && Cpp17MoveAssignable && Cpp17Swappable)
    {
        hive_matrix(
            [&](hive_t& cont) {
                auto expect = unwrap_to_vec(cont);
                try_forbid_alloc(); // test unbuffered sort with EH allocator, and buffered sort with other allocators
                cont.sort(less_pred);
                try_allow_alloc();
                ranges::sort(expect);
                assert_equal(cont, expect);
            },
            al_1, limits_counts_mat);

        // fallback
        if constexpr (is_integral_v<raw_value_t>) {
            if constexpr (numeric_limits<raw_value_t>::max() >= 1024 && !small_al) {
                const auto src = array<raw_value_t, 1024>{0, 6, 12, 18, 22, 28, 34, 38, 44, 50, 54, 60, 66, 70, 76, 82,
                    86, 92, 98, 102, 108, 114, 118, 124, 130, 134, 140, 146, 150, 156, 162, 166, 172, 178, 182, 188,
                    194, 198, 204, 210, 214, 220, 226, 230, 236, 242, 246, 252, 258, 262, 268, 274, 278, 284, 290, 294,
                    300, 306, 310, 316, 322, 326, 332, 338, 342, 348, 354, 358, 364, 370, 374, 380, 386, 390, 396, 402,
                    406, 412, 418, 422, 428, 434, 438, 444, 450, 454, 460, 466, 470, 476, 482, 486, 492, 498, 502, 508,
                    514, 518, 524, 530, 534, 540, 546, 550, 556, 562, 566, 572, 578, 582, 588, 594, 598, 604, 610, 614,
                    620, 626, 630, 636, 642, 646, 652, 658, 662, 668, 674, 678, 1, 7, 13, 684, 19, 23, 29, 690, 35, 39,
                    45, 694, 51, 55, 61, 700, 67, 71, 77, 706, 83, 87, 93, 710, 99, 103, 109, 716, 115, 119, 125, 722,
                    131, 135, 141, 726, 147, 151, 157, 732, 163, 167, 173, 738, 179, 183, 189, 742, 195, 199, 205, 748,
                    211, 215, 221, 754, 227, 231, 237, 758, 243, 247, 253, 764, 259, 263, 269, 770, 275, 279, 285, 774,
                    291, 295, 301, 780, 307, 311, 317, 786, 323, 327, 333, 790, 339, 343, 349, 796, 355, 359, 365, 802,
                    371, 375, 381, 806, 387, 391, 397, 812, 403, 407, 413, 818, 419, 423, 429, 822, 435, 439, 445, 828,
                    451, 455, 461, 834, 467, 471, 477, 838, 483, 487, 493, 844, 499, 503, 509, 850, 515, 519, 525, 854,
                    531, 535, 541, 860, 547, 551, 557, 866, 563, 567, 573, 870, 579, 583, 589, 876, 595, 599, 605, 882,
                    611, 615, 621, 886, 627, 631, 637, 892, 643, 647, 653, 898, 659, 663, 669, 902, 675, 679, 685, 908,
                    691, 695, 701, 914, 707, 711, 717, 918, 723, 727, 733, 924, 739, 743, 749, 930, 755, 759, 765, 934,
                    771, 775, 781, 940, 787, 791, 797, 946, 803, 807, 813, 950, 819, 823, 829, 956, 835, 839, 845, 962,
                    851, 855, 861, 966, 867, 871, 877, 972, 883, 887, 893, 978, 899, 903, 909, 982, 915, 919, 925, 988,
                    931, 935, 941, 990, 947, 951, 957, 992, 963, 967, 973, 1024, 979, 983, 993, 994, 995, 996, 997, 998,
                    999, 1000, 1001, 1002, 2, 20, 8, 14, 24, 36, 30, 40, 52, 46, 56, 68, 62, 72, 84, 78, 88, 100, 94,
                    104, 116, 110, 120, 132, 126, 136, 148, 142, 152, 164, 158, 168, 180, 174, 184, 196, 190, 200, 212,
                    206, 216, 228, 222, 232, 244, 238, 248, 260, 254, 264, 276, 270, 280, 292, 286, 296, 308, 302, 312,
                    324, 318, 328, 340, 334, 344, 356, 350, 360, 372, 366, 376, 388, 382, 392, 404, 398, 408, 420, 414,
                    424, 436, 430, 440, 452, 446, 456, 468, 462, 472, 484, 478, 488, 500, 494, 504, 516, 510, 520, 532,
                    526, 536, 548, 542, 552, 564, 558, 568, 580, 574, 584, 596, 590, 600, 612, 606, 616, 628, 622, 632,
                    644, 638, 648, 660, 654, 664, 676, 670, 512, 3, 991, 9, 773, 768, 15, 680, 901, 21, 522, 25, 777,
                    527, 31, 692, 965, 37, 528, 41, 960, 778, 47, 686, 905, 53, 538, 57, 936, 543, 63, 696, 1007, 69,
                    544, 73, 789, 784, 79, 708, 1014, 85, 554, 89, 793, 559, 95, 702, 969, 101, 560, 105, 911, 794, 111,
                    712, 974, 117, 570, 121, 948, 575, 127, 724, 1015, 133, 576, 137, 805, 800, 143, 718, 917, 149, 586,
                    153, 809, 591, 159, 728, 1008, 165, 592, 169, 970, 810, 175, 740, 921, 181, 602, 185, 942, 607, 191,
                    734, 1009, 197, 608, 201, 821, 816, 207, 744, 975, 213, 618, 217, 825, 623, 223, 756, 1005, 229,
                    624, 233, 927, 826, 239, 750, 984, 245, 634, 249, 952, 639, 255, 760, 1010, 261, 640, 265, 837, 832,
                    271, 772, 933, 277, 650, 281, 841, 655, 287, 766, 981, 293, 656, 297, 976, 842, 303, 776, 937, 309,
                    666, 313, 964, 671, 319, 788, 1011, 325, 672, 329, 853, 848, 335, 782, 1016, 341, 682, 345, 857,
                    687, 351, 792, 985, 357, 688, 361, 943, 858, 367, 804, 1003, 373, 698, 377, 958, 703, 383, 798,
                    1017, 389, 704, 393, 869, 864, 399, 808, 949, 405, 714, 409, 873, 719, 415, 820, 1012, 421, 720,
                    425, 986, 874, 431, 814, 953, 437, 730, 441, 968, 735, 447, 824, 1013, 453, 736, 457, 885, 880, 463,
                    836, 989, 469, 746, 473, 889, 751, 479, 830, 1006, 485, 752, 489, 959, 890, 495, 840, 1004, 501,
                    762, 505, 980, 767, 511, 852, 4, 517, 10, 521, 16, 896, 26, 846, 32, 533, 42, 537, 48, 783, 58, 856,
                    64, 549, 74, 553, 80, 906, 90, 868, 96, 565, 106, 569, 112, 799, 122, 862, 128, 581, 138, 585, 144,
                    912, 154, 72, 160, 597, 170, 601, 176, 815, 186, 884, 192, 613, 202, 617, 208, 922, 218, 878, 224,
                    629, 234, 633, 240, 831, 250, 888, 256, 645, 266, 649, 272, 928, 282, 900, 288, 661, 298, 665, 304,
                    847, 314, 894, 320, 677, 330, 681, 336, 938, 346, 904, 352, 693, 362, 697, 368, 863, 378, 916, 384,
                    709, 394, 713, 400, 944, 410, 910, 416, 725, 426, 729, 432, 879, 442, 920, 448, 741, 458, 745, 464,
                    954, 474, 932, 480, 757, 490, 761, 496, 895, 506, 926, 5, 11, 17, 27, 33, 43, 49, 59, 65, 75, 81,
                    91, 97, 107, 113, 123, 129, 139, 145, 155, 161, 71, 177, 187, 193, 203, 209, 219, 225, 235, 241,
                    251, 257, 267, 273, 283, 289, 299, 305, 315, 321, 331, 337, 347, 353, 363, 369, 379, 385, 395, 401,
                    411, 417, 427, 433, 443, 449, 459, 465, 475, 481, 491, 497, 507, 513, 523, 529, 539, 545, 555, 561,
                    571, 577, 587, 593, 603, 609, 619, 625, 635, 641, 651, 657, 667, 673, 683, 689, 699, 705, 715, 721,
                    731, 737, 747, 753, 763, 769, 779, 785, 795, 801, 811, 817, 827, 833, 843, 849, 859, 865, 875, 881,
                    891, 897, 907, 913, 923, 929, 939, 945, 955, 961, 971, 977, 987, 1018, 1019, 1020, 1021, 1022};
                const auto expect = make_unique<array<raw_value_t, 1024>>(src);
                ranges::sort(*expect);
                for (const auto& [limits, _] : limits_counts_mat) {
                    hive_t cont(from_range, src, limits, al_1);
                    try_forbid_alloc();
                    cont.sort(less_pred);
                    try_allow_alloc();
                    assert_equal(cont, *expect);
                }
            }
        }
    }

    void test_get_iterator() {
        hive_matrix(
            [&](hive_t& cont) {
                for (auto iter = cont.begin(); iter != cont.end(); ++iter) {
                    assert(cont.get_iterator(pointer_traits<ptr_t>::pointer_to(*iter)) == iter);
                    assert(cont.get_iterator(pointer_traits<cptr_t>::pointer_to(*iter)) == iter);
                }
            },
            al_1, limits_counts_mat);
    }

    // also including `advance`, `distance`, and three-way comparison
    void test_iteration() {
        hive_matrix(
            [](hive_t& cont) {
                const auto cont_size = cont.size();
                const auto cont_diff = static_cast<diff_t>(cont_size);
                const auto half_diff = static_cast<diff_t>(cont_diff / 2);

                const auto test = [&]<class First, class Last>(const First first, const Last last) {
                    auto iter = first;
                    advance(iter, cont_diff);
                    assert(iter == last);
                    advance(iter, -cont_diff);
                    assert(iter == first);
                    ranges::advance(iter, cont_diff);
                    assert(iter == last);
                    ranges::advance(iter, -cont_diff);
                    assert(iter == first);
                    advance(iter, cont_size);
                    assert(iter == last);

                    const auto middle = next(first, half_diff);

                    diff_t i = cont_diff;
                    for (; i != half_diff; --i) {
                        assert(iter > middle);
                        assert((iter <=> middle) == strong_ordering::greater);
                        --iter;
                        assert(iter < last);
                        assert((iter <=> last) == strong_ordering::less);
                    }
                    assert(iter == middle);
                    assert((iter <=> middle) == strong_ordering::equal);
                    for (; i != 0; --i) {
                        assert(iter > first);
                        assert((iter <=> first) == strong_ordering::greater);
                        --iter;
                        assert(iter < middle);
                        assert((iter <=> middle) == strong_ordering::less);
                    }
                    assert(iter == first);
                    assert((iter <=> first) == strong_ordering::equal);

                    for (; i != half_diff; ++i) {
                        assert(iter < middle);
                        assert((iter <=> middle) == strong_ordering::less);
                        ++iter;
                        assert(iter > first);
                        assert((iter <=> first) == strong_ordering::greater);
                    }
                    assert(iter == middle);
                    assert((iter <=> middle) == strong_ordering::equal);
                    for (; i != cont_diff; ++i) {
                        assert(iter < last);
                        assert((iter <=> last) == strong_ordering::less);
                        ++iter;
                        assert(iter > middle);
                        assert((iter <=> middle) == strong_ordering::greater);
                    }
                    assert(iter == last);
                    assert((iter <=> last) == strong_ordering::equal);

                    assert(prev(last, cont_diff) == first);
                    assert(next(first, cont_diff) == last);
                    assert(ranges::prev(last, cont_diff) == first);
                    assert(ranges::next(first, cont_diff) == last);

                    if constexpr (is_same_v<First, Last>) {
                        assert(distance(first, last) == cont_diff);
                    }
                    assert(ranges::distance(first, last) == cont_diff);
                };

                test(cont.begin(), cont.end());
                test(cont.begin(), cont.cend());
                test(cont.cbegin(), cont.end());
                test(cont.cbegin(), cont.cend());

                test(cont.rbegin(), cont.rend());
                test(cont.rbegin(), cont.crend());
                test(cont.crbegin(), cont.rend());
                test(cont.crbegin(), cont.crend());
            },
            al_1, limits_counts_mat);

        assert(iter_t{} == iter_t{});
        assert((citer_t{} <=> iter_t{}) == strong_ordering::equal);
        assert(next(iter_t{}, 0) == iter_t{});
        assert(ranges::next(riter_t{}, 0) == riter_t{});
        assert(distance(iter_t{}, iter_t{}) == 0);
        assert(ranges::distance(riter_t{}, riter_t{}) == 0);
    }

    void test_EH()
        requires (EH_al && EH_wrapper);

    void test_all() {
        static_assert(static_test());

        test_limits();
        test_ctors();
        test_assign();
        test_reserve();
        DO_IF_VALID(test_shrink_to_fit());
        test_trim_capacity();
        DO_IF_VALID(test_reshape());
        test_insert();
        test_erase();
        test_swap();
        test_splice();
        DO_IF_VALID(test_sort());
        test_unique();
        test_get_iterator();
        test_iteration();

        DO_IF_VALID(test_EH());
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

namespace EH {
    struct operation_counts {
        size_t allocation   = 0;
        size_t construction = 0;
        size_t assignment   = 0;

        void reset() {
            allocation = construction = assignment = 0;
        }
        bool operator==(const operation_counts&) const = default;
    };
    struct heap_states {
        size_t leaked_mem_bytes = 0;
        size_t leaked_mem_count = 0;
        size_t leaked_obj_count = 0;

        bool operator==(const heap_states&) const = default;
    };
    struct throw_countdown {
        optional<size_t> allocation   = nullopt;
        optional<size_t> construction = nullopt;
        optional<size_t> assignment   = nullopt;

        void reset() {
            allocation = construction = assignment = nullopt;
        }
    };

    struct my_bad_alloc : bad_alloc {};
    struct my_bad_construct {};
    struct my_bad_assign {};

    // Use global states to avoid increasing wrapper size and test `sizeof(T) == 1` scenarios.
    operation_counts global_counts;
    heap_states global_heap_states;
    throw_countdown global_countdown;

    void forbid_alloc() {
        global_countdown.allocation = 0uz;
    }
    void allow_alloc() {
        global_countdown.allocation = nullopt;
    }

    void on_allocate(size_t bytes) {
        global_countdown.allocation = global_countdown.allocation.transform([](size_t countdown) {
            if (countdown == 0) {
                throw my_bad_alloc{};
            }
            return countdown - 1;
        });

        ++global_counts.allocation;
        ++global_heap_states.leaked_mem_count;
        global_heap_states.leaked_mem_bytes += bytes;
    }
    void on_deallocate(size_t bytes) noexcept {
        --global_heap_states.leaked_mem_count;
        global_heap_states.leaked_mem_bytes -= bytes;
    }

    void on_construct() {
        global_countdown.construction = global_countdown.construction.transform([](size_t countdown) {
            if (countdown == 0) {
                throw my_bad_construct{};
            }
            return countdown - 1;
        });

        ++global_counts.construction;
        ++global_heap_states.leaked_obj_count;
    }
    void on_destroy() noexcept {
        --global_heap_states.leaked_obj_count;
    }

    void on_assign() {
        global_countdown.assignment = global_countdown.assignment.transform([](size_t countdown) {
            if (countdown == 0) {
                throw my_bad_assign{};
            }
            return countdown - 1;
        });

        ++global_counts.assignment;
    }

    template <class T>
    struct wrapper : wrappers::wrapper_base {
        T value;
        static_assert(is_nothrow_copy_assignable_v<T>);
        static_assert(is_nothrow_move_assignable_v<T>);

        wrapper() = default;
        /* implicit */ wrapper(T unwrapped) : value(unwrapped) {}

        wrapper(const wrapper&) = default;
        wrapper(wrapper&&)      = default;

        wrapper& operator=(const wrapper& other) {
            value = other.value; // intentionally no strong guarantee
            on_assign();
            return *this;
        }
        wrapper& operator=(wrapper&& other) {
            value = move(other.value); // intentionally no strong guarantee
            on_assign();
            return *this;
        }
    };

    template <class T>
    struct EH_allocator {
        using value_type = T;

        size_t id = 0;

        EH_allocator() = default;
        constexpr explicit EH_allocator(size_t id_) noexcept : id(id_) {}

        template <class U>
        constexpr explicit EH_allocator(const EH_allocator<U>& other) noexcept : id(other.id) {}

        constexpr T* allocate(size_t cnt) {
            on_allocate(cnt * sizeof(T));
            return allocator<T>{}.allocate(cnt);
        }
        constexpr void deallocate(T* ptr, size_t cnt) noexcept {
            allocator<T>{}.deallocate(ptr, cnt);
            on_deallocate(cnt * sizeof(T));
        }

        template <class... Args>
        constexpr void construct(T* p, Args&&... args) {
            construct_at(p, forward<Args>(args)...); // intentionally no strong guarantee
            on_construct();
        }
        constexpr void destroy(T* p) noexcept {
            destroy_at(p);
            on_destroy();
        }

        constexpr EH_allocator select_on_container_copy_construction() const noexcept {
            return EH_allocator{id + 1000};
        }

        bool operator==(const EH_allocator&) const = default;
    };

    operation_counts init_counts;
    vector<pair<operation_counts, operation_counts>> recorded_counts;
    bool recording = false;
    void do_not_test_above() {
        if (recording) {
            init_counts = global_counts;
        }
    }
    void do_not_test_below() {
        if (recording && init_counts != global_counts) {
            recorded_counts.emplace_back(init_counts, global_counts);
            init_counts = global_counts;
        }
    }

    // Runs `func`, recording all allocations, assignments, and constructions;
    // then repeatedly reruns `func`, throwing at each previously recorded throwing point.
    // Use `do_not_test_above` and `do_not_test_below` to suppress throws.
    template <class Fn>
    void test(Fn func) {
        recorded_counts.clear();
        global_counts.reset();
        const auto init_heap_states = global_heap_states;

        recording = true;
        do_not_test_above();
        func();
        do_not_test_below();
        recording = false;
        assert(global_heap_states == init_heap_states);

        for (const auto& [begin_counts, end_counts] : recorded_counts) {
            for (size_t alloc_idx = begin_counts.allocation; alloc_idx != end_counts.allocation; ++alloc_idx) {
                global_countdown.allocation = alloc_idx;
                assert_throw<my_bad_alloc>(func);
                assert(global_heap_states == init_heap_states);
            }
            global_countdown.allocation = nullopt;

            for (size_t cons_idx = begin_counts.construction; cons_idx != end_counts.construction; ++cons_idx) {
                global_countdown.construction = cons_idx;
                assert_throw<my_bad_construct>(func);
                assert(global_heap_states == init_heap_states);
            }
            global_countdown.construction = nullopt;

            for (size_t assign_idx = begin_counts.assignment; assign_idx != end_counts.assignment; ++assign_idx) {
                global_countdown.assignment = assign_idx;
                assert_throw<my_bad_assign>(func);
                assert(global_heap_states == init_heap_states);
            }
            global_countdown.assignment = nullopt;
        }
    }

    struct throw_pred_err {};

    struct throw_bool {
        optional<bool> value;
        /* implicit */ operator bool() const {
            return value ? *value : throw throw_pred_err{};
        }

        throw_bool operator!() const noexcept {
            return {value.transform([](bool val) { return !val; })};
        }
    };
    static_assert(boolean_testable<throw_bool>);

    template <class Pred>
    struct throw_pred {
        Pred pred;
        size_t countdown;

        throw_pred(const Pred& pr, size_t cd) : pred(pr), countdown(cd) {}

        throw_pred(const throw_pred&)            = delete;
        throw_pred& operator=(const throw_pred&) = delete;

        template <class... Args>
        throw_bool operator()(Args&&... args) noexcept {
            if (countdown == 0) {
                return {nullopt};
            }
            --countdown;
            return {pred(forward<Args>(args)...)};
        }
    };

    template <class Fn, class Pred>
    void test_pred(Fn func, Pred pred) {
        const auto init_heap_state = global_heap_states;

        size_t pred_call_count;
        {
            counted_pred counter{pred};
            func(ref(counter));
            pred_call_count = counter.cnt;
        }

        for (size_t throw_on = 0; throw_on != pred_call_count; ++throw_on) {
            throw_pred tpred{pred, throw_on};
            assert_throw<throw_pred_err>([&] { func(ref(tpred)); });
            assert(global_heap_states == init_heap_state);
        }
    }
} // namespace EH

template <class Alloc, class Maker, class T, class EqualPred, class LessPred>
void tests<Alloc, Maker, T, EqualPred, LessPred>::test_EH()
    requires (EH_al && EH_wrapper)
{
    using namespace EH;

    const auto hive_mat_EH = [&](auto func, Alloc& al, const hive_limits& limits, size_ty cnt) {
        const auto rnd_engine_state = rand_engine;
        hive_fn_matrix(
            [&](auto get_hive) {
                EH::test([&] {
                    rand_engine     = rnd_engine_state;
                    const auto cont = get_hive();
                    do_not_test_above();
                    func(*cont);
                });
            },
            al, limits, cnt);
    };

    // ctor
    for (const auto& [limits, counts] : limits_counts_mat) {
        for (const auto& cnt : counts) {
            // default fill
            EH::test([&] { hive_t cont(cnt, limits, al_1); });
            // fill
            {
                const T val{gen_raw_value()};
                EH::test([&] { hive_t cont(cnt, val, limits, al_1); });
            }
            // range
            range_matrix<false>(
                [&](auto get_rng) {
                    if constexpr (ranges::common_range<decltype(get_rng())>) {
                        EH::test([&] {
                            auto&& rg = get_rng();
                            do_not_test_above();
                            hive_t cont(ranges::begin(rg), ranges::end(rg), limits, al_1);
                        });
                    }

                    EH::test([&] {
                        auto&& rg = get_rng();
                        do_not_test_above();
                        hive_t cont(from_range, rg, limits, al_1);
                    });
                },
                al_1, cnt);
            // copy
            hive_matrix([&](const hive_t& src) { EH::test([&] { hive_t dst(src, al_1); }); }, al_1, limits, cnt);
            // move
            hive_mat_EH([&](hive_t& src) { hive_t dst(move(src), al_1); }, al_2, limits, cnt);
        }
    }

    // assign
    for (const auto& [limits, counts] : limits_counts_mat_reduced) {
        for (const auto& old_cnt : counts) {
            // ilist
            {
                const auto raw_vec = gen_raw_rng(5) | ranges::to<vector>();
                const auto ilist   = {T{raw_vec[0]}, T{raw_vec[1]}, T{raw_vec[2]}, T{raw_vec[3]}, T{raw_vec[4]}};
                hive_mat_EH([&](hive_t& cont) { cont.assign(ilist); }, al_1, limits, old_cnt);
            }
            for (const auto& target_cnt : counts) {
                // fill
                {
                    const T val{gen_raw_value()};
                    hive_mat_EH([&](hive_t& cont) { cont.assign(target_cnt, val); }, al_1, limits, old_cnt);
                }
                // range
                range_matrix<false>(
                    [&](auto get_rng) {
                        if constexpr (ranges::common_range<decltype(get_rng())>) {
                            hive_mat_EH(
                                [&](hive_t& cont) {
                                    auto&& rg = get_rng();
                                    do_not_test_above();
                                    cont.assign(ranges::begin(rg), ranges::end(rg));
                                },
                                al_1, limits, old_cnt);
                        }

                        hive_mat_EH(
                            [&](hive_t& cont) {
                                auto&& rg = get_rng();
                                do_not_test_above();
                                cont.assign_range(rg);
                            },
                            al_1, limits, old_cnt);
                    },
                    al_1, target_cnt);
            }
        }
    }
    // copy assign
    hive_matrix(
        [&](const hive_t& right) {
            for (const auto& [limits, counts] : limits_counts_mat_reduced) {
                for (const auto& cnt : counts) {
                    hive_mat_EH([&](hive_t& left) { left = right; }, al_1, limits, cnt);
                }
            }
        },
        al_1, limits_counts_mat_reduced);
    // move assign
    for (const auto& [r_limits, r_counts] : limits_counts_mat_reduced) {
        for (const auto& r_cnt : r_counts) {
            for (const auto& [l_limits, l_counts] : limits_counts_mat_reduced) {
                for (const auto& l_cnt : l_counts) {
                    hive_fn_matrix(
                        [&](auto get_right) {
                            hive_mat_EH([&](hive_t& left) { left = move(*get_right()); }, al_2, l_limits, l_cnt);
                        },
                        al_1, r_limits, r_cnt);
                }
            }
        }
    }

    for (const auto& [limits, counts] : limits_counts_mat) {
        for (const auto& cnt : counts) {
            // reserve
            hive_mat_EH([&](hive_t& cont) { cont.reserve(cont.capacity() + cnt); }, al_1, limits, cnt);
            // shrink_to_fit
            hive_mat_EH([&](hive_t& cont) { cont.shrink_to_fit(); }, al_1, limits, cnt);
            // reshape
            for (const auto& [new_limits, _] : limits_counts_mat) {
                hive_mat_EH([&](hive_t& cont) { cont.reshape(new_limits); }, al_1, limits, cnt);
            }
        }
    }

    // insert
    for (const auto& [limits, counts] : limits_counts_mat) {
        for (const auto& cnt : counts) {
            // emplace (strong guarantee)
            {
                const auto raw_val = gen_raw_value();
                hive_matrix(
                    [&](hive_t& cont) {
                        strong_guarantee_state state{cont};
                        const auto heap_states = global_heap_states;

                        global_countdown.construction = 0uz;
                        assert_throw<my_bad_construct>([&] { cont.emplace(raw_val); });
                        global_countdown.construction = nullopt;

                        state.assert_eq(cont);
                        assert(heap_states == global_heap_states);
                    },
                    al_1, limits, cnt);
            }
            // fill
            {
                const T val{gen_raw_value()};
                hive_mat_EH([&](hive_t& cont) { cont.insert(cnt, val); }, al_1, limits, cnt);
            }
            // ilist
            {
                const auto raw_vec = gen_raw_rng(5) | ranges::to<vector>();
                const auto ilist   = {T{raw_vec[0]}, T{raw_vec[1]}, T{raw_vec[2]}, T{raw_vec[3]}, T{raw_vec[4]}};
                hive_mat_EH([&](hive_t& cont) { cont.insert(ilist); }, al_1, limits, cnt);
            }
            // range
            range_matrix<false>(
                [&](auto get_rng) {
                    if constexpr (ranges::common_range<decltype(get_rng())>) {
                        hive_mat_EH(
                            [&](hive_t& dst) {
                                auto&& rg = get_rng();
                                do_not_test_above();
                                dst.insert(ranges::begin(rg), ranges::end(rg));
                            },
                            al_1, limits, cnt);
                    }

                    hive_mat_EH(
                        [&](hive_t& dst) {
                            auto&& rg = get_rng();
                            do_not_test_above();
                            dst.insert_range(rg);
                        },
                        al_1, limits, cnt);
                },
                al_1, cnt);
        }
    }

    const auto hive_mat_EH_pr = [&](auto func, Alloc& al, const hive_limits& limits, size_ty cnt, auto pred) {
        const auto rnd_engine_state = rand_engine;
        hive_fn_matrix(
            [&](auto get_hive) {
                EH::test_pred(
                    [&](auto pr) {
                        rand_engine = rnd_engine_state;
                        func(*get_hive(), pr);
                    },
                    pred);
            },
            al, limits, cnt);
    };

    constexpr auto true_pred  = [](auto&&...) { return bool_constant<true>{}; };
    constexpr auto false_pred = [](auto&&...) { return bool_constant<false>{}; };

    for (const auto& [limits, counts] : limits_counts_mat) {
        for (const auto& cnt : counts) {
            // erase_if
            hive_mat_EH_pr([&](hive_t& cont, auto pr) { erase_if(cont, pr); }, al_1, limits, cnt, true_pred);
            hive_mat_EH_pr([&](hive_t& cont, auto pr) { erase_if(cont, pr); }, al_1, limits, cnt, false_pred);

            hive_mat_EH_pr(
                [&](hive_t& cont, auto pr) {
                    const auto vals = unwrap_to_vec(cont);
                    counted_pred counted_pr{pr};
                    try {
                        erase_if(cont, ref(counted_pr));
                    } catch (...) {
                        // N5032 [hive.erasure]/2
                        assert_equal(cont, vals | views::drop(static_cast<ptrdiff_t>(counted_pr.cnt - 1)));
                        throw;
                    }
                },
                al_1, limits, cnt, true_pred);

            // sort
            hive_mat_EH_pr([&](hive_t& cont, auto pr) { cont.sort(pr); }, al_1, limits, cnt, less_pred);
            // unique
            hive_mat_EH_pr([&](hive_t& cont, auto pr) { cont.unique(pr); }, al_1, limits, cnt, true_pred);
            hive_mat_EH_pr([&](hive_t& cont, auto pr) { cont.unique(pr); }, al_1, limits, cnt, false_pred);
        }
    }
}

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
    {
        const auto init_states = EH::global_heap_states;
        oper(tests{EH::EH_allocator<T>{1}, EH::EH_allocator<T>{2}, args...});
        assert(init_states == EH::global_heap_states);
    }

    // special
    {
        const auto null_al = max_size_0_allocator<T>{};
        assert(null_al.max_size() == 0);
        tests{null_al, null_al, args...}.test_limits();
    }

    static_assert(is_same_v<pmr::hive<T>, hive<T, pmr::polymorphic_allocator<T>>>);
    static_assert(is_same_v<hive<T>, hive<T, allocator<T>>>);
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

    {
        using alloc = EH::EH_allocator<EH::wrapper<Raw>>;
        tests{alloc{1}, alloc{2}, maker<Raw>}.test_EH();
    }
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

    // giant element limits
    {
        using value_type = array<uint8_t, 0x7fffffff - 1>;
        const allocator<value_type> al{};
        tests{al, al, [](auto&&...) -> vector<value_type> { abort(); }}.test_limits();
    }

    // indirect sorting
    {
        using value_type = array<uint64_t, 4>;
        const allocator<value_type> al{};
        tests{al, al, maker<value_type>}.test_sort();
    }

    static_assert(noexcept(hive_limits{0uz, 0uz}));

    // nonstandard test, SCARY
    static_assert(is_same_v<hive<int>::iterator, pmr::hive<int>::iterator>);
}
