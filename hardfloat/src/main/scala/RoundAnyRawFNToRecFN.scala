
/*============================================================================

This Chisel source file is part of a pre-release version of the HardFloat IEEE
Floating-Point Arithmetic Package, by John R. Hauser (with some contributions
from Yunsup Lee and Andrew Waterman, mainly concerning testing).

Copyright 2010, 2011, 2012, 2013, 2014, 2015, 2016, 2017 The Regents of the
University of California.  All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

 1. Redistributions of source code must retain the above copyright notice,
    this list of conditions, and the following disclaimer.

 2. Redistributions in binary form must reproduce the above copyright notice,
    this list of conditions, and the following disclaimer in the documentation
    and/or other materials provided with the distribution.

 3. Neither the name of the University nor the names of its contributors may
    be used to endorse or promote products derived from this software without
    specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS "AS IS", AND ANY
EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, ARE
DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

=============================================================================*/

package hardfloat

import chisel3._
import chisel3.util.Fill
import consts._

//----------------------------------------------------------------------------
//----------------------------------------------------------------------------

/**
  *
  *
  * @param inSigWidth sig + 2
  * @param outSigWidth sig
  *
  * sig: input width = sig + 2, 2 for Guard bit and (R +S)
  *
  *
  */
class
    RoundAnyRawFNToRecFN(
        inExpWidth: Int,
        inSigWidth: Int,
        outExpWidth: Int,
        outSigWidth: Int,
        options: Int
    )
    extends RawModule
{
    val io = IO(new Bundle {
        val invalidExc  = Input(Bool())   // overrides 'infiniteExc' and 'in'
        val infiniteExc = Input(Bool())   // overrides 'in' except for 'in.sign'
        val in = Input(new RawFloat(inExpWidth, inSigWidth))
                                        // (allowed exponent range has limits)
        val roundingMode   = Input(UInt(3.W))
        val detectTininess = Input(UInt(1.W))
        val out = Output(Bits((outExpWidth + outSigWidth + 1).W))
        val exceptionFlags = Output(Bits(5.W))
    })

    //------------------------------------------------------------------------
    //------------------------------------------------------------------------
    // false when option = 0
    val sigMSBitAlwaysZero = ((options & flRoundOpt_sigMSBitAlwaysZero) != 0)
    /** todo */
    val effectiveInSigWidth =
        if (sigMSBitAlwaysZero) inSigWidth else inSigWidth + 1
    /** for low to high */
    val neverUnderflows =
        ((options &
              (flRoundOpt_neverUnderflows | flRoundOpt_subnormsAlwaysExact)
         ) != 0) ||
            (inExpWidth < outExpWidth)
  /** for low to high */
    val neverOverflows =
        ((options & flRoundOpt_neverOverflows) != 0) ||
            (inExpWidth < outExpWidth)
    val outNaNExp = BigInt(7)<<(outExpWidth - 2)
    val outInfExp = BigInt(6)<<(outExpWidth - 2)
    val outMaxFiniteExp = outInfExp - 1
    /** 18 */
    val outMinNormExp = (BigInt(1)<<(outExpWidth - 1)) + 2
    /** 8 */
    val outMinNonzeroExp = outMinNormExp - outSigWidth + 1

    //------------------------------------------------------------------------
    //------------------------------------------------------------------------
    val roundingMode_near_even   = (io.roundingMode === round_near_even)
    val roundingMode_minMag      = (io.roundingMode === round_minMag)
    val roundingMode_min         = (io.roundingMode === round_min)
    val roundingMode_max         = (io.roundingMode === round_max)
    val roundingMode_near_maxMag = (io.roundingMode === round_near_maxMag)
    val roundingMode_odd         = (io.roundingMode === round_odd)

    val roundMagUp =
        (roundingMode_min && io.in.sign) || (roundingMode_max && ! io.in.sign)

    //------------------------------------------------------------------------
    //------------------------------------------------------------------------
    val sAdjustedExp =
        if (inExpWidth < outExpWidth)
            (io.in.sExp +&
                 ((BigInt(1)<<outExpWidth) - (BigInt(1)<<inExpWidth)).S
            )(outExpWidth, 0).zext
        else if (inExpWidth == outExpWidth) // general case
            io.in.sExp
        else
            io.in.sExp +&
                ((BigInt(1)<<outExpWidth) - (BigInt(1)<<inExpWidth)).S
    val adjustedSig =
        if (inSigWidth <= outSigWidth + 2)// general case adjustedSig =  io.in.sig
            io.in.sig<<(outSigWidth - inSigWidth + 2)
        else
            (io.in.sig(inSigWidth, inSigWidth - outSigWidth - 1) ##
                io.in.sig(inSigWidth - outSigWidth - 2, 0).orR
            )
    /** sig msb */
    val doShiftSigDown1 =
        if (sigMSBitAlwaysZero) false.B else adjustedSig(outSigWidth + 2)

    val common_expOut   = Wire(UInt((outExpWidth + 1).W))
    val common_fractOut = Wire(UInt((outSigWidth - 1).W))
    val common_overflow       = Wire(Bool())
    val common_totalUnderflow = Wire(Bool())
    val common_underflow      = Wire(Bool())
    val common_inexact        = Wire(Bool())

    if (// for f16 to f64
        neverOverflows && neverUnderflows
            && (effectiveInSigWidth <= outSigWidth)
    ) {

        //--------------------------------------------------------------------
        //--------------------------------------------------------------------
      // sig msb = 1 means adder overflow , so exp + 1
        common_expOut := sAdjustedExp(outExpWidth, 0) + doShiftSigDown1
        common_fractOut :=
            Mux(doShiftSigDown1,
                adjustedSig(outSigWidth + 1, 3),
                adjustedSig(outSigWidth, 2)
            )
        common_overflow       := false.B
        common_totalUnderflow := false.B
        common_underflow      := false.B
        common_inexact        := false.B

    } else { // normal case

        //--------------------------------------------------------------------
        //--------------------------------------------------------------------
        val roundMask =
            if (neverUnderflows)
                0.U(outSigWidth.W) ## doShiftSigDown1 ## 3.U(2.W)
            else
                (lowMask(
                        sAdjustedExp(outExpWidth, 0), // leave the first bit
                        outMinNormExp - outSigWidth - 1,
                        outMinNormExp
                    ) | doShiftSigDown1) ##
                  3.U(2.W)

        val shiftedRoundMask = 0.U(1.W) ## roundMask>>1
        /** select the first bit need to be  rounded*/
        val roundPosMask = ~shiftedRoundMask & roundMask
        /** need to add ulp or not */
        val roundPosBit = (adjustedSig & roundPosMask).orR
        /** Any bits is one after guard bit */
        val anyRoundExtra = (adjustedSig & shiftedRoundMask).orR
        /** Any bits is one containing guard bit */
        val anyRound = roundPosBit || anyRoundExtra

        /** round increment */
        val roundIncr =
            ((roundingMode_near_even || roundingMode_near_maxMag) &&
                 roundPosBit) ||
                (roundMagUp && anyRound)
        /** width = sig +2
          *
          * when round mask = 0011  => xxxx
          *                   0111  => xxx0
          *
          *
          * */
        val roundedSig: Bits =
            Mux(roundIncr,
                (((adjustedSig | roundMask)>>2) +& 1.U) & // containing cases for mask = 0111 and 0011
                    ~Mux(roundingMode_near_even && roundPosBit && // for round to even when 0.5 happens
                             ! anyRoundExtra,
                         roundMask>>1,
                         0.U((outSigWidth + 2).W)
                     ),
                (adjustedSig & ~roundMask)>>2 | // containing cases for mask = 0111 and 0011
                    Mux(roundingMode_odd && anyRound, roundPosMask>>1, 0.U)
            )
//*** IF SIG WIDTH IS VERY NARROW, NEED TO ACCOUNT FOR ROUND-EVEN ZEROING
//***  M.S. BIT OF SUBNORMAL SIG?
        /** @todo (roundedSig>>outSigWidth) is just msb in adjustedSig? */
        val sRoundedExp = sAdjustedExp +& (roundedSig>>outSigWidth).asUInt.zext

        common_expOut := sRoundedExp(outExpWidth, 0)
        common_fractOut :=
            Mux(doShiftSigDown1,
                roundedSig(outSigWidth - 1, 1),
                roundedSig(outSigWidth - 2, 0)
            )
        common_overflow :=
            (if (neverOverflows) false.B else
//*** REWRITE BASED ON BEFORE-ROUNDING EXPONENT?:
                 (sRoundedExp>>(outExpWidth - 1) >= 3.S))
        common_totalUnderflow :=
            (if (neverUnderflows) false.B else
//*** WOULD BE GOOD ENOUGH TO USE EXPONENT BEFORE ROUNDING?:
                 (sRoundedExp < outMinNonzeroExp.S))

        val unboundedRange_roundPosBit =
            Mux(doShiftSigDown1, adjustedSig(2), adjustedSig(1))
        val unboundedRange_anyRound =
            (doShiftSigDown1 && adjustedSig(2)) || adjustedSig(1, 0).orR
        val unboundedRange_roundIncr =
            ((roundingMode_near_even || roundingMode_near_maxMag) &&
                 unboundedRange_roundPosBit) ||
                (roundMagUp && unboundedRange_anyRound)
        val roundCarry =
            Mux(doShiftSigDown1,
                roundedSig(outSigWidth + 1),
                roundedSig(outSigWidth)
            )
        common_underflow :=
            (if (neverUnderflows) false.B else
                 common_totalUnderflow ||
//*** IF SIG WIDTH IS VERY NARROW, NEED TO ACCOUNT FOR ROUND-EVEN ZEROING
//***  M.S. BIT OF SUBNORMAL SIG?
                     (anyRound && ((sAdjustedExp>>outExpWidth) <= 0.S) &&
                          Mux(doShiftSigDown1, roundMask(3), roundMask(2)) &&
                          ! ((io.detectTininess === tininess_afterRounding) &&
                                 ! Mux(doShiftSigDown1,
                                       roundMask(4),
                                       roundMask(3)
                                   ) &&
                                 roundCarry && roundPosBit &&
                                 unboundedRange_roundIncr)))

        common_inexact := common_totalUnderflow || anyRound
    }

    //------------------------------------------------------------------------
    //------------------------------------------------------------------------
    val isNaNOut = io.invalidExc || io.in.isNaN
    val notNaN_isSpecialInfOut = io.infiniteExc || io.in.isInf
    val commonCase = ! isNaNOut && ! notNaN_isSpecialInfOut && ! io.in.isZero
    val overflow  = commonCase && common_overflow
    val underflow = commonCase && common_underflow
    val inexact = overflow || (commonCase && common_inexact)

    val overflow_roundMagUp =
        roundingMode_near_even || roundingMode_near_maxMag || roundMagUp
    val pegMinNonzeroMagOut =
        commonCase && common_totalUnderflow && (roundMagUp || roundingMode_odd)
    val pegMaxFiniteMagOut = overflow && ! overflow_roundMagUp
    val notNaN_isInfOut =
        notNaN_isSpecialInfOut || (overflow && overflow_roundMagUp)

    val signOut = Mux(isNaNOut, false.B, io.in.sign)
    val expOut =
        (common_expOut &
             ~Mux(io.in.isZero || common_totalUnderflow,
               (BigInt(7)<<(outExpWidth - 2)).U((outExpWidth + 1).W),
               0.U
              ) &
             ~Mux(pegMinNonzeroMagOut,
                  ~outMinNonzeroExp.U((outExpWidth + 1).W),
               0.U
              ) &
             ~Mux(pegMaxFiniteMagOut,
               (BigInt(1)<<(outExpWidth - 1)).U((outExpWidth + 1).W),
               0.U
              ) &
             ~Mux(notNaN_isInfOut,
               (BigInt(1)<<(outExpWidth - 2)).U((outExpWidth + 1).W),
               0.U
              )) |
            Mux(pegMinNonzeroMagOut,
              outMinNonzeroExp.U((outExpWidth + 1).W),
              0.U
            ) |
            Mux(pegMaxFiniteMagOut,
              outMaxFiniteExp.U((outExpWidth + 1).W),
              0.U
            ) |
            Mux(notNaN_isInfOut, outInfExp.U((outExpWidth + 1).W), 0.U) |
            Mux(isNaNOut,        outNaNExp.U((outExpWidth + 1).W), 0.U)
    val fractOut =
        Mux(isNaNOut || io.in.isZero || common_totalUnderflow,
            Mux(isNaNOut, (BigInt(1)<<(outSigWidth - 2)).U, 0.U),
            common_fractOut
        ) |
        Fill(outSigWidth - 1, pegMaxFiniteMagOut)

    io.out := signOut ## expOut ## fractOut
    io.exceptionFlags :=
        io.invalidExc ## io.infiniteExc ## overflow ## underflow ## inexact
}

//----------------------------------------------------------------------------
//----------------------------------------------------------------------------

class
    RoundRawFNToRecFN(expWidth: Int, sigWidth: Int, options: Int)
    extends RawModule
{
    val io = IO(new Bundle {
        val invalidExc  = Input(Bool())   // overrides 'infiniteExc' and 'in'
        val infiniteExc = Input(Bool())   // overrides 'in' except for 'in.sign'
        val in = Input(new RawFloat(expWidth, sigWidth + 2))
        val roundingMode   = Input(UInt(3.W))
        val detectTininess = Input(UInt(1.W))
        val out = Output(Bits((expWidth + sigWidth + 1).W))
        val exceptionFlags = Output(Bits(5.W))
    })

    val roundAnyRawFNToRecFN =
        Module(
            new RoundAnyRawFNToRecFN(
                    expWidth, sigWidth + 2, expWidth, sigWidth, options))
    roundAnyRawFNToRecFN.io.invalidExc     := io.invalidExc
    roundAnyRawFNToRecFN.io.infiniteExc    := io.infiniteExc
    roundAnyRawFNToRecFN.io.in             := io.in
    roundAnyRawFNToRecFN.io.roundingMode   := io.roundingMode
    roundAnyRawFNToRecFN.io.detectTininess := io.detectTininess
    io.out            := roundAnyRawFNToRecFN.io.out
    io.exceptionFlags := roundAnyRawFNToRecFN.io.exceptionFlags
}

