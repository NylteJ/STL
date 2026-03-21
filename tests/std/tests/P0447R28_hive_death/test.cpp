#include <cstddef>
#include <cstdint>
#include <hive>
#include <iterator>

#include <test_death.hpp>

using namespace std;

template <class T>
class tests {
private:
    using hive_t = hive<T>;
    using iter_t = hive_t::iterator;

    using get_iterator_fn = iter_t (*)(hive_t&);

    static iter_t begin_iter(hive_t& cont) {
        return cont.begin();
    }
    static iter_t end_iter(hive_t& cont) {
        return cont.end();
    }
    static iter_t value_inited_iter(hive_t&) {
        return iter_t{};
    }
    static iter_t invalid_iter(hive_t& cont) {
        const auto iter = cont.begin();
        cont.erase(iter);
        return iter;
    }

    template <get_iterator_fn get_iter>
    static void deref() {
        hive_t x{0, 1};
        (void) *get_iter(x);
    }
    template <get_iterator_fn get_iter>
    static void increment() {
        hive_t x{0, 1};
        (void) ++get_iter(x);
    }
    template <get_iterator_fn get_iter>
    static void decrement() {
        hive_t x{0, 1};
        (void) --get_iter(x);
    }

    template <get_iterator_fn get_iter_l, get_iterator_fn get_iter_r>
    static void spaceship() {
        hive_t x{0, 1};
        (void) (get_iter_l(x) <=> get_iter_r(x));
    }
    template <get_iterator_fn get_iter_l, get_iterator_fn get_iter_r>
    static void compare() {
        hive_t x{0, 1};
        (void) (get_iter_l(x) == get_iter_r(x));
    }

    template <get_iterator_fn get_iter_i, get_iterator_fn get_iter_s>
    static void adl_verify_range() {
        hive_t x{0, 1};
        std::_Adl_verify_range(get_iter_i(x), get_iter_s(x));
    }

    template <get_iterator_fn get_iter>
    static void erase() {
        hive_t x{0, 1};
        x.erase(get_iter(x));
    }
    template <get_iterator_fn get_iter_i, get_iterator_fn get_iter_s>
    static void erase_rng() {
        hive_t x{0, 1};
        x.erase(get_iter_i(x), get_iter_s(x));
    }

    template <get_iterator_fn get_iter, ptrdiff_t diff>
    static void std_advance() {
        hive_t x{0, 1};
        auto iter = get_iter(x);
        advance(iter, diff);
    }
    template <get_iterator_fn get_iter, ptrdiff_t diff>
    static void ranges_advance() {
        hive_t x{0, 1};
        auto iter = get_iter(x);
        ranges::advance(iter, diff);
    }

    template <hive_limits limits>
    static void ctor_limits() {
        (void) hive_t(limits);
    }
    template <hive_limits limits>
    static void reshape_limits() {
        hive_t x;
        x.reshape(limits);
    }

    static void insert_overlap() {
        hive_t x{0, 1};
        x.insert(x.begin(), next(x.begin()));
    }
    static void insert_range_overlap() {
        hive_t x{0, 1};
        x.insert_range(x);
    }
    static void assign_overlap() {
        hive_t x{0, 1};
        x.assign(x.begin(), next(x.begin()));
    }
    static void assign_range_overlap() {
        hive_t x{0, 1};
        x.assign_range(x);
    }

    static void splice_self() {
        hive_t x;
        x.splice(x);
    }

    static void bad_get_iterator_1() {
        hive_t x{0, 1};
        hive_t another_cont{0};
        (void) x.get_iterator(&*another_cont.begin());
    }
    static void bad_get_iterator_2() {
        hive_t x{0, 1};
        const auto ptr = &*x.begin();
        x.erase(x.begin());
        (void) x.get_iterator(ptr);
    }

    static void use_after_erase() {
        hive_t x{0, 1};
        auto iter = x.begin();
        x.erase(iter);
        (void) ++iter;
    }
    static void use_after_range_erase() {
        hive_t x{0, 1};
        auto iter = x.begin();
        x.erase(x.begin(), x.end());
        (void) ++iter;
    }

    static void erase_invalidate_end_1() {
        hive_t x{0, 1};
        auto iter = x.end();
        x.erase(prev(x.end()));
        (void) ++iter;
    }
    static void erase_invalidate_end_2() {
        hive_t x{0, 1, 2};
        auto iter = x.end();
        x.erase(next(x.begin()), x.end());
        (void) ++iter;
    }

public:
    static void test_all(std_testing::death_test_executive& exec) {
        exec.add_death_tests({
#if _ITERATOR_DEBUG_LEVEL != 0
            deref<end_iter>,
            deref<value_inited_iter>,
            deref<invalid_iter>,

            increment<end_iter>,
            increment<value_inited_iter>,
            increment<invalid_iter>,

            decrement<begin_iter>,
            decrement<value_inited_iter>,
            decrement<invalid_iter>,

            spaceship<begin_iter, value_inited_iter>,
            spaceship<invalid_iter, begin_iter>,
            spaceship<end_iter, value_inited_iter>,
            spaceship<invalid_iter, end_iter>,
            spaceship<invalid_iter, invalid_iter>,

            compare<begin_iter, value_inited_iter>,
            compare<invalid_iter, begin_iter>,
            compare<end_iter, value_inited_iter>,
            compare<invalid_iter, end_iter>,
            compare<invalid_iter, invalid_iter>,

            adl_verify_range<begin_iter, value_inited_iter>,
            adl_verify_range<invalid_iter, begin_iter>,
            adl_verify_range<end_iter, value_inited_iter>,
            adl_verify_range<invalid_iter, end_iter>,
            adl_verify_range<invalid_iter, invalid_iter>,
            adl_verify_range<end_iter, begin_iter>,

            erase<end_iter>,
            erase<value_inited_iter>,
            erase<invalid_iter>,

            erase_rng<value_inited_iter, value_inited_iter>,

            std_advance<begin_iter, -1>,
            std_advance<end_iter, 1>,
            std_advance<begin_iter, 100>,
            std_advance<end_iter, -100>,
            std_advance<value_inited_iter, 1>,
            std_advance<invalid_iter, -1>,

            ranges_advance<begin_iter, -1>,
            ranges_advance<end_iter, 1>,
            ranges_advance<begin_iter, 100>,
            ranges_advance<end_iter, -100>,
            ranges_advance<value_inited_iter, 1>,
            ranges_advance<invalid_iter, -1>,

            ctor_limits<hive_limits{2, 1}>,
            ctor_limits<hive_limits{0, 1}>,
            ctor_limits<hive_limits{1, 142857}>,

            reshape_limits<hive_limits{2, 1}>,
            reshape_limits<hive_limits{0, 1}>,
            reshape_limits<hive_limits{1, 142857}>,

            insert_overlap,
            insert_range_overlap,

            assign_overlap,
            assign_range_overlap,
#endif // _ITERATOR_DEBUG_LEVEL != 0

            splice_self,

#if _MSVC_STL_HARDENING_HIVE || _ITERATOR_DEBUG_LEVEL != 0
            bad_get_iterator_1,
#endif // _MSVC_STL_HARDENING_HIVE || _ITERATOR_DEBUG_LEVEL != 0

#if _ITERATOR_DEBUG_LEVEL != 0
            bad_get_iterator_2,

            use_after_erase,
            use_after_range_erase,

            erase_invalidate_end_1,
            erase_invalidate_end_2,
#endif // _ITERATOR_DEBUG_LEVEL != 0
        });
    }
};

int main(int argc, char* argv[]) {
    std_testing::death_test_executive exec;

    tests<uint8_t>::test_all(exec);
    tests<uint16_t>::test_all(exec);
    tests<uint64_t>::test_all(exec);

    return exec.run(argc, argv);
}
