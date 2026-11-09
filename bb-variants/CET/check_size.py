import subprocess

code = """
#include <iostream>
#include <cstdint>
struct Tr { uint8_t w; int8_t m; uint8_t n; };
struct Mach2 { Tr t[2][4][3]; };
int main() {
    std::cout << "sizeof(Tr)=" << sizeof(Tr) << " sizeof(Mach2)=" << sizeof(Mach2) << std::endl;
    return 0;
}
"""
with open("/mnt/c/Users/Rowan/Documents/catch em/test_size.cpp", "w") as f:
    f.write(code)

subprocess.run(["g++", "/mnt/c/Users/Rowan/Documents/catch em/test_size.cpp", "-o", "/mnt/c/Users/Rowan/Documents/catch em/test_size"])
p = subprocess.run(["/mnt/c/Users/Rowan/Documents/catch em/test_size"], capture_output=True, text=True)
print(p.stdout)
