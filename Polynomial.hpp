#ifndef DIOPHANTINE_EQUATIONS_POLYNOMIAL_HPP_INCLUDED
#define DIOPHANTINE_EQUATIONS_POLYNOMIAL_HPP_INCLUDED

#include <array>       // for std::array
#include <cstddef>     // for std::size_t
#include <cstdint>     // for std::uintmax_t
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


template <std::size_t NUM_VARS>
struct Term {


    Monomial<NUM_VARS> monom;
    T_COEFF coeff;


    explicit constexpr Term(
        const Monomial<NUM_VARS> &monomial, T_COEFF coefficient
    )
        : monom(monomial)
        , coeff(coefficient) {}


    template <typename T>
    constexpr T evaluate(const std::array<T, NUM_VARS> &x) const noexcept {
        static_assert(std::is_signed<T>::value);
        T result = static_cast<T>(coeff);
        for (std::size_t i = 0; i < NUM_VARS; ++i) {
            result *= pow(x[i], monom.get_exponent(i));
        }
        return result;
    }


    constexpr void negate() noexcept { coeff = -coeff; }


    constexpr void negate_variable(std::size_t i) noexcept {
        if (monom.get_exponent(i) & 1) { coeff = -coeff; }
    }


    constexpr std::size_t hash() const noexcept {
        constexpr std::size_t SHIFT =
            static_cast<std::size_t>(0x9E3779B97F4A7C15ULL);
        constexpr std::size_t MULTIPLIER =
            static_cast<std::size_t>(0x517CC1B727220A94ULL);
        std::size_t result = static_cast<std::size_t>(coeff) * MULTIPLIER;
        for (std::size_t i = 0; i < NUM_VARS; ++i) {
            result ^=
                static_cast<std::size_t>(monom.get_exponent(i)) * MULTIPLIER +
                SHIFT + (result << 6) + (result >> 2);
        }
        return result;
    }


}; // struct Term


static_assert(sizeof(Term<1>) == sizeof(T_EXPONENT) + sizeof(T_COEFF));
static_assert(sizeof(Term<2>) == 2 * sizeof(T_EXPONENT) + sizeof(T_COEFF));
static_assert(sizeof(Term<3>) == 3 * sizeof(T_EXPONENT) + sizeof(T_COEFF));
static_assert(sizeof(Term<4>) == 4 * sizeof(T_EXPONENT) + sizeof(T_COEFF));


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


template <std::size_t NUM_VARS>
struct Polynomial : public std::vector<Term<NUM_VARS>> {


    template <typename T>
    constexpr T evaluate(const std::array<T, NUM_VARS> &x) const noexcept {
        static_assert(std::is_signed<T>::value);
        T result = static_cast<T>(0);
        for (const Term<NUM_VARS> &term : *this) { result += term.evaluate(x); }
        return result;
    }


    template <typename T>
    constexpr bool has_root_in_radius(const T &radius) const noexcept {
        L1BallIterator<T, NUM_VARS> ball_iterator(radius);
        do {
            if (evaluate(ball_iterator.get_point()) == 0) { return true; }
        } while (ball_iterator.increment());
        return false;
    }


    constexpr bool uses_variable(std::size_t i) const noexcept {
        for (const Term<NUM_VARS> &term : *this) {
            if (term.monom.get_exponent(i) != 0) { return true; }
        }
        return false;
    }


    constexpr bool uses_all_variables() const noexcept {
        for (std::size_t i = 0; i < NUM_VARS; ++i) {
            if (!uses_variable(i)) { return false; }
        }
        return true;
    }


    constexpr bool has_constant_term() const noexcept {
        for (const Term<NUM_VARS> &term : *this) {
            if (term.monom.is_constant()) { return true; }
        }
        return false;
    }


    constexpr bool has_linear_variable(std::size_t i) const noexcept {
        for (const Term<NUM_VARS> &term : *this) {
            if (!(term.monom.is_constant_in(i) || term.monom.is_linear_in(i))) {
                return false;
            }
        }
        return true;
    }


    constexpr bool has_linear_variable() const noexcept {
        for (std::size_t i = 0; i < NUM_VARS; ++i) {
            if (has_linear_variable(i)) { return true; }
        }
        return false;
    }


    constexpr void swap_variables(std::size_t i, std::size_t j) noexcept {
        for (Term<NUM_VARS> &term : *this) { term.monom.swap_variables(i, j); }
    }


    constexpr void rotate_variables_left() noexcept {
        for (Term<NUM_VARS> &term : *this) {
            term.monom.rotate_variables_left();
        }
    }


    constexpr void rotate_variables_right() noexcept {
        for (Term<NUM_VARS> &term : *this) {
            term.monom.rotate_variables_right();
        }
    }


    constexpr void negate() noexcept {
        for (Term<NUM_VARS> &term : *this) { term.negate(); }
    }


    constexpr void negate_variable(std::size_t i) noexcept {
        for (Term<NUM_VARS> &term : *this) { term.negate_variable(i); }
    }


    constexpr std::size_t hash() const noexcept {
        std::size_t result = 0;
        for (const Term<NUM_VARS> &term : *this) { result += term.hash(); }
        return result;
    }


}; // struct Polynomial


template <std::size_t NUM_VARS>
std::ostream &
operator<<(std::ostream &os, const Polynomial<NUM_VARS> &polynomial) {

    static_assert(NUM_VARS <= 26);

    if (polynomial.empty()) {
        os << '0';
        return os;
    }

    bool first = true;
    for (const Term<NUM_VARS> &term : polynomial) {

        const bool sign = (term.coeff < 0);
        if (first) {
            if (sign) { os << '-'; }
            first = false;
        } else {
            os << (sign ? " - " : " + ");
        }

        const T_COEFF abs_coeff = sign ? -term.coeff : term.coeff;
        if ((abs_coeff != 1) || term.monom.is_constant()) {
            os << static_cast<long long int>(abs_coeff);
        }

        for (std::size_t i = 0; i < NUM_VARS; ++i) {
            const T_EXPONENT exponent = term.monom.get_exponent(i);
            if (exponent != 0) {
                os << static_cast<char>(((NUM_VARS <= 3) ? 'x' : 'a') + i);
                if (exponent != 1) {
                    os << '^';
                    os << static_cast<long long int>(exponent);
                }
            }
        }
    }
    return os;
}


} // namespace DiophantineEquations

#endif // DIOPHANTINE_EQUATIONS_POLYNOMIAL_HPP_INCLUDED
