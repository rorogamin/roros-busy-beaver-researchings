
#include <iostream>
#include <cstdint>
struct Tr { uint8_t w; int8_t m; uint8_t n; };
struct Mach2 { Tr t[2][4][3]; };
int main() {
    std::cout << "sizeof(Tr)=" << sizeof(Tr) << " sizeof(Mach2)=" << sizeof(Mach2) << std::endl;
    return 0;
}
