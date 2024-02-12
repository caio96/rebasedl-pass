# Region Packing Pass

Identifies opportunities for region-based structure splitting, field reordering, and data packing.
It is run as a link-time optimization, but it can also be run as a regular function pass.
Based on [LLVM Tutor](https://github.com/banach-space/llvm-tutor).
## Build Instructions

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
git clone -b llvmorg-16.0.0 https://github.com/llvm/llvm-project.git
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
cmake --install . --prefix /path/to/llvm/install
```

### Build Region Packing Pass

1. Set these variables to the correct paths and export them:

```sh
export LLVM_INSTALL="/path/to/llvm/install"
export REGION_PACKING_ROOT="/path/to/region-packing-pass"
```

2. Build the out-of-tree pass:

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

Option 1 is how the pass was tested and used.
For the other options, adjustments may be needed.

1. Use the pass as a link time pass:

```sh
${LLVM_INSTALL}/bin/clang \
        -disable-output \
        -g -O3 \
        -flto \
        -fuse-ld=%{LLVM_INSTALL}/bin/ld.lld \
        -Wl,--load-pass-plugin=${REGION_PACKING_ROOT}/build/lib/libMannarswamyImprovePass.so \
        input.c
```

2. The pass can also be used as a pass plugin run from `opt`:

```sh
${LLVM_INSTALL}/bin/opt \
        -disable-output \
        -load-pass-plugin ${REGION_PACKING_ROOT}/build/lib/libRebaseDLPass.so \
        -passes=rebasedl \
        input.ll
```

3. In the function `getRebaseDLPassPluginInfo()`, register the pass using `registerVectorizerStartEPCallback()` to use it as a function pass.
   Then, it can be used with the following command:

```sh
${LLVM_INSTALL}/bin/clang \
        -disable-output \
        -g -O3 \
        -fpass-plugin=${REGION_PACKING_ROOT}/build/lib/libMannarswamyImprovePass.so \
        input.c
```

