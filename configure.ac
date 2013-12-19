dnl ********************************************************************
dnl Process this file with autoconf to produce a configure script.
dnl ********************************************************************
AC_INIT([insight],[0.3])
AC_CONFIG_AUX_DIR([autotools-files])
AC_CONFIG_MACRO_DIR([autotools-files/m4])
AC_CONFIG_HEADERS([src/config.h])

# Otherwise the default may include -O2
#CFLAGS=
#CXXFLAGS=

dnl Customize the src/config.h
AH_TOP([/* Defining a robust NORETURN attribute */
#if (__GNUC__ > 2 || (__GNUC__ == 2 && __GNUC_MINOR__ >= 5))
#define NORETURN __attribute__ ((noreturn))
#else
#define NORETURN
#endif

/* Defining a robust UNUSED attribute */
#if (__GNUC__ > 2 || (__GNUC__ == 2 && __GNUC_MINOR__ >= 5))
#define UNUSED __attribute__ ((unused))
#else
#define UNUSED
#endif])

AM_INIT_AUTOMAKE
AM_MAINTAINER_MODE

AC_LANG([C++])

dnl ********************************************************************
dnl Checking for standard programs, headers and libraries
dnl ********************************************************************
AC_SEARCH_LIBS([strerror],[cposix])
AC_PROG_CXX
AC_PROG_CC
AM_PROG_CC_C_O
AM_PROG_LIBTOOL

AC_SEARCH_LIBS([dlopen], [dl dld], [], [
   AC_MSG_ERROR([unable to find the dlopen() function])
])

AC_PROG_LEX
if test "x$LEX" = "x:" ; then
   AC_MSG_ERROR(['flex' cannot be found])
fi

AC_PROG_YACC
if test "x$YACC" = "x:" ; then
   AC_MSG_ERROR(['bison' cannot be found])
fi


dnl ********************************************************************
dnl Checking for test framework (ATF with Kyua)
dnl ********************************************************************

PKG_CHECK_MODULES([ATF_CXX], [atf-c++ >= 0.14],
	          [with_atf="yes"],
	          [with_atf="no";
	           AC_MSG_WARN([ATF >= 0.14 not found. Disabling tests...])])

if test x$with_atf = xyes ; then
   CPPFLAGS="${CPPFLAGS} ${ATF_CXX_CFLAGS}"
   LDFLAGS="${LDFLAGS} ${ATF_CXX_LIBS}"
   AC_CHECK_HEADERS([atf-c++.hpp], [with_atf="yes"],
		    [with_atf="no";
		     AC_MSG_WARN([ATF header files not found. Disabling tests...])])
fi

if test x$with_atf = xyes ; then
   AC_CHECK_PROG(with_kyua, [kyua], [yes], [no])
   if test x$with_kyua = xno ; then
      with_atf="no"
      AC_MSG_WARN([Kyua not found. Disabling tests...])
   fi
fi

AM_CONDITIONAL([WITH_ATF], [test x$with_atf = xyes])

dnl ********************************************************************
dnl Check existence of Valgrind for test
dnl ********************************************************************

AC_ARG_ENABLE(valgrind,
              AS_HELP_STRING([--enable-valgrind],
			     [enable Valgrind for in test suite (default is no)]),
              ENABLE_VALGRIND=$enableval,
              ENABLE_VALGRIND=no)

if test "x${ENABLE_VALGRIND}" = "xyes"; then
   AC_CHECK_PROG(with_valgrind, [valgrind], [yes], [no])	
   if test x$with_valgrind = xno ; then
       AC_MSG_WARN([Valgrind not found. Disabling memory leaks checks for tests])
   fi
else
   with_valgrind=no
fi

AM_CONDITIONAL([WITH_VALGRIND], [test x$with_valgrind = xyes])


dnl ********************************************************************
dnl Option and variable settings
dnl ********************************************************************

dnl Initial settings of flags variables
CFLAGS="${CFLAGS} -Wall -Wextra -D_FORTIFY_SOURCE=2"
CXXFLAGS="${CXXFLAGS} -Wall -Wextra -D_FORTIFY_SOURCE=2"
CPPFLAGS="${CPPFLAGS}"
LDFLAGS="${LDFLAGS}"
LIBS="${LIBS}"

dnl Full verification activated (handle with care!)
dnl EXTRA_FLAGS= \
dnl         "-pedantic -Weffc++ -Wstrict-overflow -Woverloaded-virtual" \
dnl         "-Wsign-promo -Wabi -Wmissing-declarations -Wconversion"    \
dnl	    "-Wuninitialized -Wcast-align -Wredundant-decls"

AC_CANONICAL_HOST
case $host_os in
     *linux*)
        HOST_OS=linux
	LIBS="${LIBS}"
	;;
     *bsd*)
        HOST_OS=bsd
	CPPFLAGS="-I/usr/pkg/include ${CPPFLAGS} -DBSD"
	LDFLAGS="${LDFLAGS} -L/usr/pkg/lib"
	LIBS="${LIBS} -lz -liberty -lintl"
	;;
     *cygwin*)
        HOST_OS=cygwin
	LIBS="${LIBS} -lz -liberty -lintl"
	;;
     *darwin*)
        HOST_OS=darwin
	CPPFLAGS="${CPPFLAGS} -I/opt/local/include"
	LDFLAGS="${LDFLAGS} -L/opt/local/lib"
	LIBS="${LIBS} -lz -liberty -lintl"
	;;
     *)
	AC_MSG_WARN([OS unknown: going further with no warranty])
	;;
esac

dnl Parsing and setting options on compile flags
AC_ARG_ENABLE(werror,
              AS_HELP_STRING([--enable-werror],
			     [compile with -Werror flag (default is no)]),
              ENABLE_WERROR=$enableval,
              ENABLE_WERROR=no)

AC_ARG_ENABLE(debug,
              AS_HELP_STRING([--enable-debug],
			     [compile with debug (default is no)]),
              ENABLE_DEBUG=$enableval,
              ENABLE_DEBUG=no)

if test x$ENABLE_DEBUG = xyes ; then
    CFLAGS="${CFLAGS} -g -DDEBUG"
    CXXFLAGS="${CXXFLAGS} -g -DDEBUG"
fi

AC_ARG_ENABLE(optimization,
              AS_HELP_STRING([--enable-optimization],
			     [compile with optimization (default is no)]),
              ENABLE_OPTIMIZE=$enableval,
              ENABLE_OPTIMIZE=no)

if test x$ENABLE_OPTIMIZE = xyes ; then
    CFLAGS="${CFLAGS} -O2"
    CXXFLAGS="${CXXFLAGS} -O2"
fi


dnl ********************************************************************
dnl Checking for specific programs, headers and libraries
dnl ********************************************************************


dnl Checking for MathSAT solver
AC_CHECK_PROG([has_mathsat_solver], [mathsat], [yes], [no])
if test ${has_mathsat_solver} = "yes"; then
   MATHSAT_VERSION=`mathsat -version | cut -d " " -f 3`

   MATHSAT_VERSION_MAJOR=`echo ${MATHSAT_VERSION} | cut -d "." -f 1`
   MATHSAT_VERSION_MINOR=`echo ${MATHSAT_VERSION} | cut -d "." -f 2`
   MATHSAT_VERSION_PATCH=`echo ${MATHSAT_VERSION} | cut -d "." -f 3`

   if test "${MATHSAT_VERSION_MAJOR}" != "5"; then
      has_mathsat_solver="warning! (version 5.0.0 or beyond is prefered)"
   fi

   if test "${MATHSAT_VERSION_MINOR}" = "2" -a  \
           "${MATHSAT_VERSION_PATCH}" -ge "7" -a \
           "$HOST_OS" = "darwin"; then
	   LIBS="${LIBS} -lstdc++ -lc++"
   fi
   AC_DEFINE([HAVE_MATHSAT_SOLVER],[1])
else
   AC_DEFINE([HAVE_MATHSAT_SOLVER],[0],[Defined to 1 if MathSAT is installed])
fi

if test "${MATHSAT_VERSION}" = ""; then
   MATHSAT_VERSION="	"
fi

have_libgmp=no
AC_SEARCH_LIBS([__gmp_version], [gmp],
	       [have_libgmp=yes],
	       [AC_MSG_WARN(['mathsat' library (-lmathsat) cannot be found])])

have_libmathsat=no
AC_SEARCH_LIBS([msat_get_version], [mathsat],
	       [have_libmathsat=yes],
	       [AC_MSG_WARN(['mathsat' library (-lmathsat) cannot be found])])

have_mathsat_h=no
AC_CHECK_HEADERS([mathsat.h],
                 [have_mathsat_h=yes],
                 [AC_MSG_WARN(['mathsat.h' cannot be found])])

AC_DEFINE([INTEGRATED_MATHSAT_SOLVER], [], 
          [Defined to 1 if MATHSAT solver has to be integrated.])

have_integrated_mathsat=no
if test "${have_mathsat_h}" = "yes" -a "${have_libmathsat}" = "yes" \
        -a "${have_libgmp}" = "yes"; then
   have_integrated_mathsat=yes
   AC_DEFINE([INTEGRATED_MATHSAT_SOLVER], [1])
   AC_MSG_NOTICE([integrate MATHSAT API.])
else
   AC_DEFINE([INTEGRATED_MATHSAT_SOLVER], [0])
fi

dnl Checking for Z3 solver
AC_CHECK_PROG([has_z3_solver], [z3], [yes], [no])
if test ${has_z3_solver} = "yes"; then
   Z3_VERSION="`z3 --version | cut -d " " -f 3`"

   Z3_VERSION_MAJOR=`echo ${Z3_VERSION} | cut -d "." -f 1`
   Z3_VERSION_MINOR=`echo ${Z3_VERSION} | cut -d "." -f 2`
   Z3_VERSION_PATCH=`echo ${Z3_VERSION} | cut -d "." -f 3`

   if test "${Z3_VERSION_MAJOR}" != "4" -o \
           "${Z3_VERSION_MINOR}" != "3" -o \
	    "${Z3_VERSION_PATCH}" -lt "2"; then
      has_z3_solver="warning! (version 4.3.2 or beyond is prefered)"
   fi

   AC_DEFINE([HAVE_Z3_SOLVER],[1])
else
    AC_DEFINE([HAVE_Z3_SOLVER],[0],[Defined to 1 if Z3 is installed])
fi

if test "${Z3_VERSION}" = ""; then
   Z3_VERSION="	"
fi

if test "${has_z3_solver}" = yes; then
	default_solver_command=z3
	default_solver_args="-smt2 -in"
	have_solver=yes
	default_solver=process
elif test "${has_mathsat_solver}" != no; then
	default_solver_command=mathsat
	default_solver_args=
	have_solver=yes
	default_solver=process
else
	default_solver=no-solver-is-defined
	have_solver=no
fi

if test "${have_integrated_mathsat}" = "yes"; then
	default_solver=mathsat
	have_solver=yes
fi

AC_DEFINE([HAVE_SOLVER], [0], [Defined to 1 if at least one SMT solver has been found])
if test "${have_solver}" = "yes"; then
   AC_DEFINE([HAVE_SOLVER],[1])
fi

AM_CONDITIONAL([HAVE_SOLVER], [test x$have_solver = xyes])
AC_SUBST(HAVE_SOLVER, ${have_solver})
AC_SUBST(process_solver_command,${default_solver_command})
AC_SUBST(process_solver_args,${default_solver_args})
AC_SUBST(default_solver,${default_solver})

dnl Checking for binutils (libbfd, libopcodes)
AC_ARG_WITH([binutils-header],
	    AS_HELP_STRING(
		[--with-binutils-header=PATH],
		[force the PATH to the binutils header files]),
		[if test -n "$withval" ; then
		    BINUTILS_CFLAGS="${BINUTILS_CFLAGS} -I$withval"
		 fi],
		[])
AC_ARG_WITH([binutils-lib],
	    AS_HELP_STRING(
		[--with-binutils-lib=PATH],
		[force the PATH to the binutils libraries]),
		[if test -n "$withval" ; then
		    BINUTILS_LDFLAGS="${BINUTILS_LDFLAGS} -L$withval"
		 fi],
		[])

dnl Saving the flag values
CPPFLAGS_TMP="${CPPFLAGS}"
CPPFLAGS="${CPPFLAGS_TMP} ${BINUTILS_CFLAGS}"
LDFLAGS_TMP="${LDFLAGS}"
LDFLAGS="${LDFLAGS_TMP} ${BINUTILS_LDFLAGS}"

dnl Checking for libbfd (looking for multiarch first)
AC_SEARCH_LIBS([bfd_init], [bfd-multiarch bfd],
	       [],
	       [AC_MSG_ERROR(['binutils' library (-lbfd) cannot be found])])

AC_CHECK_HEADERS([bfd.h],
                 [],
                 [AC_MSG_ERROR([binutils 'bfd.h' cannot be found])])

dnl Checking for libopcodes(looking for multiarch first)
AC_SEARCH_LIBS([init_disassemble_info], [opcodes-multiarch opcodes],
               [],
	       [AC_MSG_ERROR(['binutils' library (-lopcodes) cannot be found])])

AC_CHECK_HEADERS([dis-asm.h],
                 [],
                 [AC_MSG_ERROR([binutils 'dis-asm.h' cannot be found])])

dnl Restoring the flag values
CPPFLAGS="${CPPFLAGS_TMP}"
LDFLAGS="${LDFLAGS_TMP}"

AC_SUBST(BINUTILS_CFLAGS)
AC_SUBST(BINUTILS_LDFLAGS)

dnl Checking for libxml2
PKG_CHECK_MODULES([XML], [libxml-2.0])

dnl
dnl Test architectures supported by libbfd
dnl

dnl Check for x86_32 and x86_64 (they share the same print_insn_*)
x86_32_support="no"
x86_64_support="no"
AC_CHECK_FUNC([print_insn_i386], [x86_32_support="yes"])
AC_CHECK_FUNC([print_insn_i386], [x86_64_support="yes"])

AM_CONDITIONAL([BFD_SUPPORTS_X86_32], [test "${x86_32_support}" = "yes"])
AM_CONDITIONAL([BFD_SUPPORTS_X86_32], [test "${x86_64_support}" = "yes"])

dnl Check for sparc support
sparc_support="no"
AC_CHECK_FUNC([print_insn_sparc], [sparc_support="yes"])

AM_CONDITIONAL([BFD_SUPPORTS_SPARC], [test "${sparc_support}" = "yes"])

dnl Check for arm support
arm_big_support="no"
AC_CHECK_FUNC([print_insn_big_arm], [arm_big_support="yes"])

arm_little_support="no"
AC_CHECK_FUNC([print_insn_little_arm], [arm_little_support="yes"])

arm_support="no"
if test "${arm_little_support}${arm_big_support}" = "yesyes"; then
   arm_support="yes"
fi

AM_CONDITIONAL([BFD_SUPPORTS_ARM], [test "${arm_support}" = "yes"])

dnl Setting the standard flags (CXXFLAGS, CPPFLAGS, LDFLAGS)
CXXFLAGS="${CXXFLAGS}"
CPPFLAGS="${CPPFLAGS} ${XML_CFLAGS} ${BINUTILS_CFLAGS}"
LDFLAGS="${LDFLAGS} ${BINUTILS_LDFLAGS} ${LDFLAGS}"
LIBS="${XML_LIBS} ${LIBS}"

dnl Locate repository of binary test-cases
TEST_SAMPLES_DIR='${abs_top_srcdir}/test/test-samples'

AC_SUBST(TEST_SAMPLES_DIR)

dnl We currently enable -Werror when in maintainer mode
dnl Enable -Werror only after all others tests to prevent configure to fail
dnl in test that compile test codes.
if test x$ENABLE_WERROR = xyes ; then
   CFLAGS="${CFLAGS} -Werror"
   CXXFLAGS="${CXXFLAGS} -Werror"
fi

dnl ********************************************************************
dnl Writing files
dnl ********************************************************************
AC_CONFIG_FILES([
	Makefile
	doc/Makefile
	doc/doxygen/doxygen.cfg
	doc/manuals/common-macros.texi
	src/Makefile
	test/Makefile
	test/Makefile.inc
	test/cfgrecovery.cfg
	test/bugs/Makefile
	test/domains/Makefile
	test/domains/concrete/Makefile
	test/domains/sets/Makefile
	test/domains/symbolic/Makefile
	test/domains/symbolic/Kyuafile
	test/io/Makefile
	test/io/xml/Makefile
	test/kernel/Makefile
	test/tools/Makefile
	test/tools/cfgrecovery/Makefile
	test/decoders/Makefile
	test/decoders/x86-32/Makefile
	test/decoders/x86-64/Makefile
	test/slicing/Makefile
	test/utils/Makefile
	tools/Makefile
	tools/cfgrecovery/Makefile
], [ ], [ ])

AC_OUTPUT

AC_MSG_NOTICE([
=================================================================
		    Insight ${VERSION}
=================================================================
Here is the configuration of the package:
    Operating System	     	: ${host_os}
    Architecture		: ${host_cpu}

    Installation prefix	     	: ${prefix}
    Source code location	: ${srcdir}

    C Compiler			: ${CC}
    C++ Compiler		: ${CXX}
    CFLAGS			: ${CFLAGS}
    CXXFLAGS			: ${CXXFLAGS}
    CPPFLAGS			: ${CPPFLAGS}
    LDFLAGS			: ${LDFLAGS}
    LIBS                        : ${LIBS}

    BINUTILS_CFLAGS		: ${BINUTILS_CFLAGS}
    BINUTILS_LDFLAGS		: ${BINUTILS_LDFLAGS}

Binutils supported architectures
    x86-32            		: ${x86_32_support}
    x86-64            		: ${x86_64_support}
    arm                 	: ${arm_support}
    sparc                 	: ${sparc_support}

Detected SMT-solvers
    MathSAT ${MATHSAT_VERSION}		: ${has_mathsat_solver}
    Integrated MathSAT		: ${have_integrated_mathsat}
    Z3 ${Z3_VERSION}			: ${has_z3_solver}

Optional Features:
    Enable debug mode		: ${ENABLE_DEBUG}
    Enable werror mode		: ${ENABLE_WERROR}
    Enable optimisation mode	: ${ENABLE_OPTIMIZE}
    Automated Test Framework	: ${with_atf}
    Valgrind test   		: ${with_valgrind}
])
