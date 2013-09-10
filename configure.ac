dnl ********************************************************************
dnl Process this file with autoconf to produce a configure script.
dnl ********************************************************************
AC_INIT([insight],[0.3])
AC_CONFIG_AUX_DIR([autotools-files])
AC_CONFIG_MACRO_DIR([autotools-files/m4])
AC_CONFIG_HEADERS([src/config.h])

# Otherwise the default may include -O2
CFLAGS=
CXXFLAGS=

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
			     [enable Valgrind for in test suite (default is yes)]),
              ENABLE_VALGRIND=$enableval,
              ENABLE_VALGRIND=yes)

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
CFLAGS="${CFLAGS} -Wall -Wextra -O -D_FORTIFY_SOURCE=2"
CXXFLAGS="${CXXFLAGS} -Wall -Wextra -O -D_FORTIFY_SOURCE=2"
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
	LIBS="${LIBS}"
	;;
     *bsd*)
	CPPFLAGS="-I/usr/pkg/include ${CPPFLAGS} -DBSD"
	LDFLAGS="${LDFLAGS} -L/usr/pkg/lib"
	LIBS="${LIBS} -lz -liberty -lintl"
	;;
     *cygwin*)
	LIBS="${LIBS} -lz -liberty -lintl"
	;;
     *darwin*)
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

   AC_DEFINE([HAVE_MATHSAT_SOLVER],[1])
else
   AC_DEFINE([HAVE_MATHSAT_SOLVER],[0],[Defined to 1 if MathSAT is installed])
fi

if test "${MATHSAT_VERSION}" = ""; then
   MATHSAT_VERSION="	"
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
	doc/doxygen.cfg
	doc/manuals/common-macros.texi
	src/Makefile
	test/Makefile
	test/Makefile.inc
	test/bugs/Makefile
	test/domains/Makefile
	test/domains/concrete/Makefile
	test/domains/sets/Makefile
	test/domains/symbolic/Makefile
	test/io/Makefile
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
    Z3 ${Z3_VERSION}			: ${has_z3_solver}

Optional Features:
    Enable debug mode		: ${ENABLE_DEBUG}
    Enable werror mode		: ${ENABLE_WERROR}
    Enable optimisation mode	: ${ENABLE_OPTIMIZE}
    Automated Test Framework	: ${with_atf}
    Valgrind test   		: ${with_valgrind}
])
