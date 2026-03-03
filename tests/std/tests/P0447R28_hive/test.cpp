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

public:
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

    // also including three-way comparison
    void test_iteration() {
        hive_matrix(
            [](hive_t& cont) {
                const auto cont_size = cont.size();
                const auto cont_diff = static_cast<diff_t>(cont_size);
                const auto half_diff = static_cast<diff_t>(cont_diff / 2);

                const auto test = [&]<class First, class Last>(const First first, const Last last) {
                    auto iter = next(first, cont_diff); // TODO: this will make more sense in the future

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
    }

    void test_EH()
        requires (EH_al && EH_wrapper);

    void test_all() {
        static_assert(static_test());

        test_limits();
        test_ctors();
        test_reserve();
        test_insert();
        test_erase();
        test_unique();
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
        }
    }

    for (const auto& [limits, counts] : limits_counts_mat) {
        for (const auto& cnt : counts) {
            // reserve
            hive_mat_EH([&](hive_t& cont) { cont.reserve(cont.capacity() + cnt); }, al_1, limits, cnt);
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

    static_assert(noexcept(hive_limits{0uz, 0uz}));

    // nonstandard test, SCARY
    static_assert(is_same_v<hive<int>::iterator, pmr::hive<int>::iterator>);
}
