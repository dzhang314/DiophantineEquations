#include "Monomial.hpp"
#include "Partitions.hpp"
#include "Polynomial.hpp"
#include "PolynomialIterator.hpp"

#include <iostream>
#include <map>

using namespace DiophantineEquations;


// template <typename T, typename U>
// std::ostream &operator<<(std::ostream &os, const std::pair<T, U> &pair) {
//     os << '(';
//     os << pair.first;
//     os << ", ";
//     os << pair.second;
//     os << ')';
//     return os;
// }


// template <typename T>
// std::ostream &operator<<(std::ostream &os, const std::vector<T> &v) {
//     os << '[';
//     bool first = true;
//     for (const T &elem : v) {
//         if (first) {
//             first = false;
//         } else {
//             os << ", ";
//         }
//         os << elem;
//     }
//     os << ']';
//     return os;
// }


int main() {

    for (T_COEFF weight = 0; weight <= 12; ++weight) {

        const auto partitions = binary_partitions<T_EXPONENT, T_COEFF>(weight);
        for (const auto &partition : partitions) {

            std::map<
                std::vector<std::pair<std::array<T_EXPONENT, 3>, T_COEFF>>,
                std::size_t>
                index_table;
            std::size_t index = 0;

            PolynomialIterator<3> iterator(partition);
            do {
                const Polynomial<3> poly = iterator.get_polynomial();
                if (poly.uses_all_variables() && poly.has_constant_term() &&
                    !poly.has_linear_variable()) {
                    const auto canonized = poly.canonical_form();
                    index_table[canonized] = index++;
                }
            } while (iterator.increment());

            iterator.reset();
            std::vector<std::array<std::size_t, 4>> adjacency_lists;

            do {
                Polynomial<3> poly = iterator.get_polynomial();
                if (poly.uses_all_variables() && poly.has_constant_term() &&
                    !poly.has_linear_variable()) {

                    poly.swap_variables(0, 1);
                    const std::size_t i_swap =
                        index_table[poly.canonical_form()];
                    poly.swap_variables(0, 1);

                    poly.rotate_variables_left();
                    const std::size_t i_rotate =
                        index_table[poly.canonical_form()];
                    poly.rotate_variables_right();

                    poly.negate();
                    const std::size_t i_negate =
                        index_table[poly.canonical_form()];
                    poly.negate();

                    poly.negate_variable(0);
                    const std::size_t i_negate_variable =
                        index_table[poly.canonical_form()];
                    poly.negate_variable(0);

                    const std::array<std::size_t, 4> adj = {
                        i_swap, i_rotate, i_negate, i_negate_variable};
                    adjacency_lists.push_back(adj);
                }
            } while (iterator.increment());

            std::vector<bool> visited(adjacency_lists.size(), false);

            for (std::size_t i = 0; i < adjacency_lists.size(); ++i) {
                if (!visited[i]) {
                    std::cout << i << std::endl;
                    visited[i] = true;
                    std::vector<std::size_t> queue;
                    for (const std::size_t j : adjacency_lists[i]) {
                        if (!visited[j]) { queue.push_back(j); }
                    }
                    while (!queue.empty()) {
                        const std::size_t j = queue.back();
                        queue.pop_back();
                        if (!visited[j]) {
                            visited[j] = true;
                            for (const std::size_t k : adjacency_lists[j]) {
                                if (!visited[k]) { queue.push_back(k); }
                            }
                        }
                    }
                }
            }
        }
    }
}
