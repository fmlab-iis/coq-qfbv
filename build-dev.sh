#!/bin/bash

SWITCHES=" \
	ocaml4.08.1-coq8.11.0-ssr1.10.0 \
	ocaml4.11.2-coq8.12.2-ssr1.11.0 \
	ocaml4.12.1-coq8.13.2-ssr1.12.0 \
	ocaml4.13.1-coq8.14.1-ssr1.13.0 \
	ocaml4.14.0-coq8.15.2-ssr1.14.0 \
"

BUILD_DIR=_build

if [[ "$1" == "clean" ]]; then
  rm -rf ${BUILD_DIR}
  exit
fi

CURRENT=`opam switch show`

for s in ${SWITCHES}; do
  echo "Building with ${s}"

  echo -n "  * Running 'opam switch'	"
  opam switch ${s} &> /dev/null
  status=$?
  if [[ ${status} == 0 ]]; then
    echo "[DONE]"
  else
    echo "[FAIL]"
    continue
  fi
  eval $(opam env)

  echo -n "  * Copying files		"
  mkdir -p ${BUILD_DIR}/${s}
  tar -c --exclude ${BUILD_DIR} --exclude "*.vo" --exclude "*.vok" --exclude "*.vos" --exclude "*.glob" * | tar -x --keep-newer-files -C ${BUILD_DIR}/${s} &> /dev/null
  echo "[DONE]"

  echo -n "  * Building Coq code		"
  make -C ${BUILD_DIR}/${s} all >${BUILD_DIR}/${s}.log 2>&1
  status=$?
  if [[ $status == 0 ]]; then
    echo "[DONE]"
    echo -n "  * Building OCaml code		"
    pushd ${BUILD_DIR}/${s}/src/ocaml &> /dev/null
    dune build &> /dev/null
    status=$?
    if [[ $status == 0 ]]; then
      echo "[DONE]"
    else
      echo "[FAIL]"
    fi
    popd &> /dev/null
  else
    echo "[FAIL]"
  fi
done

echo
echo "See the following log files for compilation details."
for s in ${SWITCHES}; do
  echo "  * ${BUILD_DIR}/${s}.log"
done

opam switch ${CURRENT}
eval $(opam env)
