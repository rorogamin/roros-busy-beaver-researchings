#!/usr/bin/env bash
set -e

echo "=========================================================="
echo "  Catch-Em-Turing High-RAM Super Hunter (Linux / Colab)"
echo "=========================================================="

CORES=$(nproc 2>/dev/null || echo 16)
MEM=$(free -h | awk '/^Mem:/ {print $2}')
echo "Detected CPU Cores: $CORES | System RAM: $MEM"

# 1. Compile with aggressive optimization
echo "Compiling hunt_all_families.cpp with GCC (-O3 -march=native -flto -pthread)..."
g++ -O3 -march=native -flto -pthread hunt_all_families.cpp -o hunt_all_families_linux

# 2. Run with all cores
echo "Launching hunter on $CORES threads..."
./hunt_all_families_linux $CORES
