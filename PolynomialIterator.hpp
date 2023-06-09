#ifndef DIOPHANTINE_EQUATIONS_POLYNOMIAL_ITERATOR_HPP_INCLUDED
#define DIOPHANTINE_EQUATIONS_POLYNOMIAL_ITERATOR_HPP_INCLUDED

#include <cstddef> // for std::size_t
#include <cstdint> // for std::uintmax_t
#include <utility> // for std::pair
#include <vector>  // for std::vector

#include "Monomial.hpp"   // for Monomial, T_COEFF, T_EXPONENT
#include "Partitions.hpp" // for decrement_partition
#include "Polynomial.hpp" // for Polynomial

namespace DiophantineEquations {


template <std::size_t NUM_VARS>
struct HomogeneousPolynomialIterator {


    std::vector<Monomial<NUM_VARS>> monomials;
    std::vector<T_COEFF> dense_partition;
    std::vector<std::pair<std::size_t, T_COEFF>> sparse_partition;
    std::uintmax_t sign_pattern;


    using index_t = std::vector<T_COEFF>::size_type;


    explicit constexpr HomogeneousPolynomialIterator(
        T_EXPONENT degree, T_COEFF weight
    ) noexcept
        : monomials(Monomial<NUM_VARS>::all_monomials(degree))
        , dense_partition(monomials.size(), static_cast<T_COEFF>(0))
        , sparse_partition()
        , sign_pattern(0) {
        dense_partition[0] = weight;
        update_sparse_partition();
    }


    constexpr void update_sparse_partition() noexcept {
        sparse_partition.clear();
        for (index_t i = 0; i < dense_partition.size(); ++i) {
            if (dense_partition[i] != 0) {
                sparse_partition.emplace_back(i, dense_partition[i]);
            }
        }
    }


    constexpr T_COEFF extract_sign(index_t i) const noexcept {
        const std::uintmax_t selected_bit = static_cast<std::uintmax_t>(1)
                                            << (sparse_partition.size() - ++i);
        return static_cast<T_COEFF>((sign_pattern & selected_bit) ? -1 : +1);
    }


    constexpr void extract_polynomial(Polynomial<NUM_VARS> &polynomial
    ) const noexcept {
        index_t i = 0;
        for (const auto &[index, coeff] : sparse_partition) {
            polynomial.emplace_back(
                monomials[index], extract_sign(i++) * coeff
            );
        }
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


    constexpr void reset() noexcept {
        T_COEFF weight = 0;
        for (index_t i = 0; i < dense_partition.size(); ++i) {
            weight += dense_partition[i];
            dense_partition[i] = 0;
        }
        dense_partition[0] = weight;
        update_sparse_partition();
        sign_pattern = 0;
    }


}; // struct HomogeneousPolynomialIterator


template <std::size_t NUM_VARS>
struct PolynomialIterator {


    std::vector<HomogeneousPolynomialIterator<NUM_VARS>> iterators;


    explicit constexpr PolynomialIterator(
        const std::vector<std::pair<T_EXPONENT, T_COEFF>> &binary_partition
    ) noexcept
        : iterators() {
        for (const auto &[degree, weight] : binary_partition) {
            iterators.emplace_back(degree, weight);
        }
    }


    constexpr Polynomial<NUM_VARS> get_polynomial() const noexcept {
        Polynomial<NUM_VARS> result;
        for (const auto &iterator : iterators) {
            iterator.extract_polynomial(result);
        }
        return result;
    }


    constexpr bool increment() noexcept {
        using index_t = typename std::vector<
            HomogeneousPolynomialIterator<NUM_VARS>>::size_type;
        for (index_t i = iterators.size(); i > 0; --i) {
            if (iterators[i - 1].increment()) { return true; }
            iterators[i - 1].reset();
        }
        return false;
    }


}; // struct PolynomialIterator


} // namespace DiophantineEquations

#endif // DIOPHANTINE_EQUATIONS_POLYNOMIAL_ITERATOR_HPP_INCLUDED
