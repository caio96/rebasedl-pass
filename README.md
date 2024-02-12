# RebaseDL Pass

LLVM out-of-tree pass that identifies opportunities for region-based structure splitting, field reordering, and data packing.
Based on [LLVM Tutor](https://github.com/banach-space/llvm-tutor).

Currently, it uses **LLVM 17.0.0**.
## Build Instructions

Set these variables to the correct paths and export them:

```sh
export LLVM_INSTALL="/path/to/llvm/install"
export REGION_PACKING_ROOT="/path/to/region-packing-pass"
```

### Build Binutils

```sh
git clone --depth 1 --branch binutils-2_39 https://sourceware.org/git/binutils-gdb.git binutils
cd binutils
mkdir build
cd build
../configure --enable-gold --enable-plugins --disable-werror
make all-gold
```

### Build and Install LLVM

```sh
git clone --depth 1 -b llvmorg-17.0.0 https://github.com/llvm/llvm-project.git
cd llvm-project
mkdir build
cd build
cmake -DLLVM_ENABLE_PROJECTS="clang;lld"                         \
      -DLLVM_TARGETS_TO_BUILD="host"                             \
      -DLLVM_PARALLEL_LINK_JOBS=2                                \
      -DLLVM_INCLUDE_BENCHMARKS=OFF                              \
      -DLLVM_INCLUDE_EXAMPLES=OFF                                \
      -DLLVM_ENABLE_ASSERTIONS=ON                                \
      -DLLVM_USE_LINKER=lld                                      \
      -DLLVM_BINUTILS_INCDIR=/path/to/binutils/include           \
      -DBUILD_SHARED_LIBS=ON                                     \
      -DCMAKE_C_COMPILER=clang                                   \
      -DCMAKE_CXX_COMPILER=clang++                               \
      -DCMAKE_BUILD_TYPE=Release                                 \
      -G Ninja ../llvm
ninja
cmake --install . --prefix ${LLVM_INSTALL}
```

### Build Region Packing Pass

```sh
cd ${REGION_PACKING_ROOT}
mkdir build
cd build
cmake -DLT_LLVM_INSTALL_DIR=${LLVM_INSTALL} \
      -DCMAKE_C_COMPILER=clang              \
      -DCMAKE_CXX_COMPILER=clang++          \
      -DCMAKE_BUILD_TYPE=Release            \
      ..
make
```

## How To Use It

1. Use the pass as a compile-time pass in the clang pipeline:

```sh
${LLVM_INSTALL}/bin/clang \
        -disable-output \
        -g -O3 -fno-unroll-loops \
        -fpass-plugin=${REGION_PACKING_ROOT}/build/lib/libRebaseDLPass.so \
        input.c
```

2. Use the pass as a link-time pass in the clang pipeline:

```sh
${LLVM_INSTALL}/bin/clang \
        -disable-output \
        -g -O3 -fno-unroll-loops \
        -flto \
        -fuse-ld=%{LLVM_INSTALL}/bin/ld.lld \
        -Wl,--load-pass-plugin=${REGION_PACKING_ROOT}/build/lib/libRebaseDLPass.so \
        input.c
```

3. The pass can also be used as a pass plugin run from `opt`:

```sh
${LLVM_INSTALL}/bin/clang \
        -g -O3 -fno-unroll-loops \
        -emit-llvm -S \
        -o input.ll \
        input.c

${LLVM_INSTALL}/bin/opt \
        -disable-output \
        -load-pass-plugin ${REGION_PACKING_ROOT}/build/lib/libRebaseDLPass.so \
        -passes=rebasedl \
        input.ll
```

To use option 1 or 2, the pass registration in `getRebaseDLPassPluginInfo()` must be updated to insert the pass either at the compile-time pipeline, or at the link-time pipeline.
