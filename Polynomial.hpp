#ifndef DIOPHANTINE_EQUATIONS_POLYNOMIAL_HPP_INCLUDED
#define DIOPHANTINE_EQUATIONS_POLYNOMIAL_HPP_INCLUDED

#include <array>       // for std::array
#include <cstddef>     // for std::size_t
#include <cstdint>     // for std::intmax_t, std::uintmax_t
#include <ostream>     // for std::ostream
#include <type_traits> // for std::is_signed
#include <utility>     // for std::pair
#include <vector>      // for std::vector

#include "Monomial.hpp" // for Monomial, T_COEFF

namespace DiophantineEquations {


template <typename T>
constexpr T pow(T x, T_EXPONENT exponent) {
    T result = static_cast<T>(1);
    for (; exponent; exponent >>= 1) {
        if (exponent & 1) { result *= x; }
        x *= x;
    }
    return result;
}


static_assert(pow<int>(0, 0) == 1);
static_assert(pow<int>(-1, 2) == 1);
static_assert(pow<int>(2, 3) == 8);


template <typename T, std::size_t NUM_VARS>
struct L1BallIterator {


    using sparse_index_t =
        typename std::vector<std::pair<std::size_t, T>>::size_type;
    static constexpr T ZERO = static_cast<T>(0);


    std::vector<std::pair<std::size_t, T>> sparse_partition;
    std::uintmax_t sign_pattern;
    std::array<T, NUM_VARS> dense_partition;


    explicit constexpr L1BallIterator(const T &radius)
        : sparse_partition()
        , sign_pattern(0)
        , dense_partition() {
        if constexpr (NUM_VARS >= 1) { dense_partition[0] = radius; }
        for (std::size_t i = 1; i < NUM_VARS; ++i) {
            dense_partition[i] = ZERO;
        }
        update_sparse_partition();
    }


    constexpr void update_sparse_partition() noexcept {
        sparse_partition.clear();
        for (std::size_t i = 0; i < NUM_VARS; ++i) {
            if (dense_partition[i] != ZERO) {
                sparse_partition.emplace_back(i, dense_partition[i]);
            }
        }
    }


    constexpr bool extract_sign(sparse_index_t i) const noexcept {
        const std::uintmax_t selected_bit = static_cast<std::uintmax_t>(1)
                                            << (sparse_partition.size() - ++i);
        return static_cast<bool>(sign_pattern & selected_bit);
    }


    constexpr std::array<T, NUM_VARS> get_point() const noexcept {
        std::array<T, NUM_VARS> result;
        for (std::size_t i = 0; i < NUM_VARS; ++i) { result[i] = ZERO; }
        sparse_index_t i = 0;
        for (const auto &[index, coeff] : sparse_partition) {
            result[index] = extract_sign(i++) ? -coeff : coeff;
        }
        return result;
    }


    constexpr bool increment() noexcept {
        const std::uintmax_t sign_max = static_cast<std::uintmax_t>(1)
                                        << sparse_partition.size();
        if (++sign_pattern < sign_max) { return true; }
        sign_pattern = 0;
        if (decrement_partition(dense_partition)) {
            update_sparse_partition();
            return true;
        }
        return false;
    }


}; // struct L1BallIterator


} // namespace DiophantineEquations

#endif // DIOPHANTINE_EQUATIONS_POLYNOMIAL_HPP_INCLUDED
