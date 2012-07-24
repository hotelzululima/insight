/*
 * simulator_test_cases.hh -- add a comment about this file
 * 
 * This file is a part of XXX SET PROJECT NAME XXX. 
 * 
 * Copyright (C) 2012 CNRS UMR 5800 & Université Bordeaux I (see AUTHORS file).
 * 
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301  USA
 */

/*!
 * \file
 * \brief
 * 
 */
#ifndef SIMULATOR_TEST_CASES_HH
# define SIMULATOR_TEST_CASES_HH

#define SIMULATED_BINARIES \
  BINARY_FILE (X86_32_BASE_1, "x86_32-simulator-01.bin") \
  BINARY_FILE (X86_32_BASE_2, "x86_32-simulator-02.bin") \
  BINARY_FILE (X86_32_BASE_3, "x86_32-simulator-03.bin") \
  BINARY_FILE (X86_32_BASE_4, "x86_32-simulator-04.bin") \
  BINARY_FILE (X86_32_BASE_5, "x86_32-simulator-05.bin") \
  \
  BINARY_FILE (X86_32_AAA, "x86_32-simulator-aaa.bin") \
  BINARY_FILE (X86_32_AAD, "x86_32-simulator-aad.bin") \
  BINARY_FILE (X86_32_AAM, "x86_32-simulator-aam.bin") \
  BINARY_FILE (X86_32_AAS, "x86_32-simulator-aas.bin") \
  BINARY_FILE (X86_32_ADD, "x86_32-simulator-add.bin") \
  BINARY_FILE (X86_32_ADCSBB, "x86_32-simulator-adcsbb.bin") \
  \
  BINARY_FILE (X86_32_BOOLEANS, "x86_32-simulator-booleans.bin") \
  BINARY_FILE (X86_32_BOUND, "x86_32-simulator-bound.bin") \
  BINARY_FILE (X86_32_BSF, "x86_32-simulator-bsf.bin") \
  BINARY_FILE (X86_32_BSR, "x86_32-simulator-bsr.bin") \
  BINARY_FILE (X86_32_BSWAP, "x86_32-simulator-bswap.bin") \
  BINARY_FILE (X86_32_BT_01, "x86_32-simulator-bt-01.bin") \
  BINARY_FILE (X86_32_BT_02, "x86_32-simulator-bt-02.bin") \
  BINARY_FILE (X86_32_BTC, "x86_32-simulator-btc.bin") \
  BINARY_FILE (X86_32_BTR, "x86_32-simulator-btr.bin") \
  BINARY_FILE (X86_32_BTS, "x86_32-simulator-bts.bin") \
  \
  BINARY_FILE (X86_32_CF, "x86_32-simulator-CF.bin") \
  BINARY_FILE (X86_32_CALL, "x86_32-simulator-call.bin") \
  BINARY_FILE (X86_32_CBW, "x86_32-simulator-cbw.bin") \
  BINARY_FILE (X86_32_CMOV, "x86_32-simulator-cmov.bin") \
  BINARY_FILE (X86_32_CMPS_01, "x86_32-simulator-cmps-01.bin") \
  BINARY_FILE (X86_32_CMPS_02, "x86_32-simulator-cmps-02.bin") \
  BINARY_FILE (X86_32_CMPXCHG, "x86_32-simulator-cmpxchg.bin") \
  BINARY_FILE (X86_32_CWDCDQ, "x86_32-simulator-cwdcdq.bin") \
  \
  BINARY_FILE (X86_32_DAADAS, "x86_32-simulator-daadas.bin") \
  BINARY_FILE (X86_32_DIV, "x86_32-simulator-div.bin") \
  \
  BINARY_FILE (X86_32_ENTERLEAVE_1, "x86_32-simulator-enter-leave-01.bin") \
  BINARY_FILE (X86_32_ENTERLEAVE_2, "x86_32-simulator-enter-leave-02.bin") \
  \
  BINARY_FILE (X86_32_IDIV, "x86_32-simulator-idiv.bin") \
  BINARY_FILE (X86_32_IMUL_01, "x86_32-simulator-imul-01.bin") \
  BINARY_FILE (X86_32_IMUL_02, "x86_32-simulator-imul-02.bin") \
  BINARY_FILE (X86_32_IMUL_03, "x86_32-simulator-imul-03.bin") \
  BINARY_FILE (X86_32_INT, "x86_32-simulator-int.bin") \
  BINARY_FILE (X86_32_INT3, "x86_32-simulator-int3.bin") \
  BINARY_FILE (X86_32_INTO_01, "x86_32-simulator-into-01.bin") \
  BINARY_FILE (X86_32_INTO_02, "x86_32-simulator-into-02.bin") \
  \
  BINARY_FILE (X86_32_LSAHF, "x86_32-simulator-lsahf.bin") \
  BINARY_FILE (X86_32_LODS, "x86_32-simulator-lods.bin") \
  BINARY_FILE (X86_32_LOOP, "x86_32-simulator-loop.bin") \
  \
  BINARY_FILE (X86_32_MOVBE, "x86_32-simulator-movbe.bin") \
  BINARY_FILE (X86_32_MOVS, "x86_32-simulator-movs.bin") \
  BINARY_FILE (X86_32_MOVSXZ, "x86_32-simulator-movsxz.bin") \
  BINARY_FILE (X86_32_MUL, "x86_32-simulator-mul.bin") \
  \
  BINARY_FILE (X86_32_NEG, "x86_32-simulator-neg.bin") \
  \
  BINARY_FILE (X86_32_POPCNT, "x86_32-simulator-popcnt.bin") \
  BINARY_FILE (X86_32_PUSHPOP_1, "x86_32-simulator-pushpop-01.bin") \
  BINARY_FILE (X86_32_PUSHPOP_2, "x86_32-simulator-pushpop-02.bin") \
  BINARY_FILE (X86_32_PUSHPOP_3, "x86_32-simulator-pushpop-03.bin") \
  BINARY_FILE (X86_32_PUSHPOP_4, "x86_32-simulator-pushpop-04.bin") \
  BINARY_FILE (X86_32_PUSHPOP_5, "x86_32-simulator-pushpop-05.bin") \
  BINARY_FILE (X86_32_PUSHPOP_6, "x86_32-simulator-pushpop-06.bin") \
  BINARY_FILE (X86_32_PUSHFPOPF, "x86_32-simulator-pushfpopf.bin") \
  BINARY_FILE (X86_32_PUSHAPOPA, "x86_32-simulator-pushapopa.bin") \
  \
  BINARY_FILE (X86_32_SCAS, "x86_32-simulator-scas.bin") \
  BINARY_FILE (X86_32_SUB, "x86_32-simulator-sub.bin") \
  BINARY_FILE (X86_32_SETCC, "x86_32-simulator-setcc.bin") \
  \
  BINARY_FILE (X86_32_XADD, "x86_32-simulator-xadd.bin") \
  BINARY_FILE (X86_32_XCHG, "x86_32-simulator-xchg.bin") \
  \
  BINARY_FILE (X86_32_GCD, "x86_32-gcd.bin")

#endif /* ! SIMULATOR_TEST_CASES_HH */
