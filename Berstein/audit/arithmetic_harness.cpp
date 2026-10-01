#define main independent_kernel_original_main
#include "independent_kernel.cpp"
#undef main

int main(int argc, char** argv) {
    audit::Verifier verifier(argv[1], argv[2]);
    char operation;
    while (std::cin >> operation) {
        if (operation == 'p' || operation == 'q') {
            audit::Range a, b;
            std::cin >> a.lower >> a.upper >> b.lower >> b.upper;
            auto result = operation == 'p' ? audit::product(a,b) : audit::quotient(a,b);
            std::cout << result.lower << ' ' << result.upper << '\n';
        } else if (operation == 't') {
            audit::Side side;
            side.tails.resize(4); side.differences.resize(16); side.transitions.resize(2);
            for (auto& e : side.transitions) std::cin >> e.endpoint[0] >> e.endpoint[1];
            audit::Integer t, u; std::cin >> t >> u;
            for (auto& d : side.differences) std::cin >> d.lower >> d.upper;
            auto result = audit::endpoint_difference(side,{0,t},{1,u});
            std::cout << result.lower << ' ' << result.upper << '\n';
        } else if (operation == 'b') {
            int parent; audit::Transition left, right;
            std::cin >> parent >> left.derivative.lower >> left.derivative.upper
                     >> right.derivative.lower >> right.derivative.upper;
            int first=-1,last=-1;
            bool ok=verifier.mapped_bins(parent,left,right,first,last);
            std::cout << ok << ' ' << first << ' ' << last << '\n';
        } else {
            return 2;
        }
    }
}
