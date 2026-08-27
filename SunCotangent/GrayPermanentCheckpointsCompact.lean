import SunCotangent.GrayPermanentDP
import SunCotangent.EagerModPack

/-!
# Compact kernel-checked Gray-scan checkpoints

This is the compact presentation of the 128 independent Gray-scan
segments.  The 129 boundary accumulators are one `Fin 129` table, and
`checkpointBlock` performs an explicit finite case split on `Fin 128`.
Every resulting branch is closed by `decide +kernel`; no native evaluator
or trusted generated proof is used.

The row sums and column totals are not checkpoint data.  They are
transported symbolically, and a natural-number induction composes all
segments into the complete scan.
-/

namespace SunCotangent
namespace CyclotomicCertificate

private abbrev EagerScanState :=
  GrayPermanentDP.State EagerModPack

private def eagerAccumulator (a1 a2 a3 a4 a5 a6 : ℕ) :
    EagerModPack :=
  (a1, (a2, (a3, (a4, (a5, a6)))))

private def checkpointAccumulator : Fin 129 → EagerModPack :=
  ![eagerAccumulator 1_136_686_007 1_942_420_174 1_200_143_215 1_654_185_606 1_747_928_605 1_159_219_991,
    eagerAccumulator 677_431_376 49_462_534 272_185_062 1_291_393_627 1_236_845_907 1_290_080_196,
    eagerAccumulator 604_574_629 385_708_987 461_561_871 1_503_215_310 1_918_312_306 995_270_876,
    eagerAccumulator 1_191_196_901 287_137_119 1_702_052_257 142_305_811 308_089_751 1_322_902_066,
    eagerAccumulator 481_050_991 118_690_972 243_198_374 1_342_748_528 872_930_323 717_040_167,
    eagerAccumulator 1_009_238_415 93_572_428 762_587_486 127_372_653 202_268_074 296_333_557,
    eagerAccumulator 557_012_592 596_564_372 1_870_588_879 1_264_425_304 890_186_396 760_816_177,
    eagerAccumulator 1_460_244_416 160_340_335 1_701_825_081 1_375_408_049 589_303_567 162_299_082,
    eagerAccumulator 236_900_964 829_189_670 1_219_279_341 1_537_450_698 602_270_949 1_454_214_613,
    eagerAccumulator 19_691_820 1_059_257_117 1_659_770_279 419_602_935 1_052_098_286 1_307_782_291,
    eagerAccumulator 197_293_337 1_859_491_108 597_086_887 1_442_871_459 714_710_616 1_186_128_274,
    eagerAccumulator 1_022_555_502 727_283_468 1_804_392_501 960_759_685 60_106_598 1_736_735_832,
    eagerAccumulator 599_063_122 1_401_584_198 452_593_950 823_717_306 877_507_241 1_037_121_127,
    eagerAccumulator 969_347_026 1_732_296_152 1_633_471_864 550_229_907 1_645_469_531 277_732_812,
    eagerAccumulator 962_609_245 88_550_920 78_708_389 1_270_668_590 35_403_537 1_226_735_439,
    eagerAccumulator 1_093_799_954 1_599_410_015 941_452_560 1_354_490_984 1_655_861_076 1_129_436_804,
    eagerAccumulator 54_949_123 1_917_866_448 1_533_885_118 1_219_911_871 1_978_797_694 1_864_525_079,
    eagerAccumulator 1_625_049_291 1_183_062_031 1_236_884_069 1_299_925_893 1_125_796_398 106_263_283,
    eagerAccumulator 1_194_288_354 646_649_349 1_972_495_008 249_562_863 1_203_597_440 1_614_430_330,
    eagerAccumulator 513_813_947 503_184_687 566_719_718 902_880_523 1_476_381_027 1_354_925_148,
    eagerAccumulator 1_683_264_042 1_051_689_787 1_388_330_811 1_264_309_585 221_908_681 759_522_262,
    eagerAccumulator 768_704_852 1_741_834_210 1_793_359_927 416_416_908 1_213_352_521 1_135_169_866,
    eagerAccumulator 1_106_119_153 592_045_808 941_073_461 1_439_116_880 1_549_284_597 1_960_253_596,
    eagerAccumulator 646_555_285 1_697_443_226 438_711_629 1_400_680_906 583_090_250 1_667_157_667,
    eagerAccumulator 1_874_380_615 1_558_637_471 1_822_284_392 127_594_350 925_928_829 305_639_862,
    eagerAccumulator 665_903_496 24_501_326 1_049_376_540 434_210_956 316_089_811 635_261_873,
    eagerAccumulator 623_517_518 1_560_804_078 1_720_286_622 257_146_409 412_334_737 522_623_557,
    eagerAccumulator 1_177_603_324 1_285_324_898 351_094_487 1_227_141_554 1_246_653_538 436_735_179,
    eagerAccumulator 1_199_721_507 658_654_274 76_852_230 1_517_315_886 914_558_699 1_434_686_995,
    eagerAccumulator 60_964_447 660_744_404 1_115_161_137 44_495_934 1_861_560_999 57_917_837,
    eagerAccumulator 1_859_777_743 811_211_124 558_624_939 1_129_034_856 1_306_574_574 1_342_121_115,
    eagerAccumulator 1_735_900_240 43_168_381 293_523_685 931_129_207 1_990_887_671 497_931_250,
    eagerAccumulator 590_473_454 1_925_896_501 362_720_054 1_709_266_503 1_359_228_080 1_528_815_910,
    eagerAccumulator 856_911_703 282_957_080 580_711_021 332_503_768 1_856_997_907 453_781_726,
    eagerAccumulator 784_537_738 761_815_978 1_867_282_126 657_206_145 1_448_470_552 1_204_908_350,
    eagerAccumulator 746_313_630 824_310_868 213_322_339 218_299_321 1_485_489_565 1_040_520_499,
    eagerAccumulator 230_770_748 1_175_544_216 555_009_684 1_147_563_139 1_853_450_177 65_135,
    eagerAccumulator 967_914_638 716_583_770 110_454_870 809_106_838 587_664_225 21_882_726,
    eagerAccumulator 1_034_363_286 268_272_879 1_488_385_738 293_315_203 1_930_029_599 1_077_780_868,
    eagerAccumulator 984_744_101 1_186_291_095 99_267_122 1_431_539_471 478_720_648 43_205_277,
    eagerAccumulator 670_956_352 324_111_145 622_492_860 1_976_615_364 80_624_165 356_254_661,
    eagerAccumulator 765_741_536 794_019_728 1_545_093_203 1_556_305_490 1_504_236_443 87_708_023,
    eagerAccumulator 288_733_725 1_171_983_012 1_279_098_929 359_191_025 1_071_195_431 21_479_371,
    eagerAccumulator 527_373_661 305_992_568 1_654_766_098 1_743_595_061 216_929_272 159_465_882,
    eagerAccumulator 1_459_962_255 285_067_367 1_505_137_374 1_691_714_344 1_450_963_211 1_485_991_126,
    eagerAccumulator 1_864_840_602 208_884_290 134_179_919 1_900_070_991 1_628_230_016 393_842_791,
    eagerAccumulator 374_190_388 210_182_151 975_054_272 1_294_587_829 1_596_382_539 368_495_019,
    eagerAccumulator 1_140_902_657 178_407_777 1_712_101_672 75_170_887 112_864_407 1_411_652_027,
    eagerAccumulator 68_725_205 939_822_861 703_236_762 1_409_474_124 410_017_846 468_628_293,
    eagerAccumulator 431_755_069 117_606_635 783_441_255 1_124_692_019 863_186_163 1_110_209_748,
    eagerAccumulator 697_069_433 1_474_863_665 1_996_091_087 126_009_255 1_721_079_456 1_284_463_109,
    eagerAccumulator 1_337_102_908 1_578_416_586 1_083_821_746 192_845_758 145_817_136 405_071_960,
    eagerAccumulator 101_204_712 124_191_202 198_250_348 1_058_633_191 1_620_090_702 280_937_997,
    eagerAccumulator 1_044_673_299 410_648_658 1_262_909_189 449_162_686 1_642_519_441 1_008_350_457,
    eagerAccumulator 1_525_780_328 852_907_324 1_300_343_416 808_790_124 1_227_867_951 1_235_449_751,
    eagerAccumulator 1_883_785_164 60_922_104 1_009_291_294 1_182_947_226 846_131_887 286_018_560,
    eagerAccumulator 353_064_974 1_143_370_155 1_271_343_469 23_780_417 524_453_129 546_865_883,
    eagerAccumulator 856_969_892 449_691_705 1_422_231_470 90_718_632 164_317_933 1_858_041_518,
    eagerAccumulator 717_995_855 71_206_923 1_328_235_762 1_005_282_322 482_673_581 1_685_442_241,
    eagerAccumulator 866_102_465 1_135_621_129 1_139_956_054 52_493_008 472_572_174 209_110_404,
    eagerAccumulator 1_598_502_615 1_622_004_492 572_732_456 1_901_124_653 1_451_309_854 1_326_283_772,
    eagerAccumulator 15_979_317 1_178_519_132 1_893_754_798 694_032_112 1_328_238_354 801_002_260,
    eagerAccumulator 778_965_623 1_057_727_652 1_563_099_197 1_540_954_065 1_444_808_918 574_094_541,
    eagerAccumulator 1_130_375_950 1_707_150_127 121_208_200 950_022_645 551_879_734 823_983_958,
    eagerAccumulator 462_744_460 346_194_618 485_859_802 1_793_133_507 1_321_679_486 1_351_457_633,
    eagerAccumulator 356_537_685 772_940_044 1_395_379_963 1_297_493_076 199_932_786 1_695_251_051,
    eagerAccumulator 1_317_151_380 1_561_084_247 1_549_190_996 1_893_519_998 275_881_789 1_482_543_715,
    eagerAccumulator 246_160_676 1_304_201_757 1_459_877_029 590_715_573 1_877_576_412 706_117_464,
    eagerAccumulator 978_842_123 1_396_698_044 355_977_777 506_499_006 1_728_788_215 961_997_861,
    eagerAccumulator 76_894_424 897_955_010 95_465_315 1_123_709_460 186_712_737 1_470_831_872,
    eagerAccumulator 739_993_442 503_983_606 888_793_752 153_044_887 1_867_504_033 647_241_007,
    eagerAccumulator 1_201_554_534 1_666_854_688 653_269_420 1_253_240_193 740_100_616 1_430_048_812,
    eagerAccumulator 766_818_917 1_397_395_343 586_811_185 1_613_754_642 1_952_765_292 601_389_648,
    eagerAccumulator 781_210_133 733_574_638 217_732_346 1_610_897_180 1_061_187_528 1_848_788_974,
    eagerAccumulator 1_248_065_524 19_178_963 1_800_256_275 1_797_200_058 267_930_044 1_662_577_675,
    eagerAccumulator 62_805_394 567_876_925 1_390_940_682 1_252_621_515 1_292_161_762 1_779_090_979,
    eagerAccumulator 1_801_499_730 623_743_917 1_088_038_208 885_618_266 76_990_125 1_731_271_285,
    eagerAccumulator 107_177_853 75_319_868 1_034_155_201 1_547_503_315 1_203_150_224 45_396_983,
    eagerAccumulator 1_771_559_846 1_101_735_294 1_494_277_676 500_462_097 1_515_867_931 1_360_459_780,
    eagerAccumulator 544_115_463 599_796_960 1_091_802_920 1_180_524_157 1_311_083_474 149_216_252,
    eagerAccumulator 1_615_103_710 630_301_129 643_272_686 105_729_825 878_488_116 608_764_220,
    eagerAccumulator 1_757_553_905 1_335_151_094 1_008_530_845 1_174_956_254 1_941_666_513 146_703_909,
    eagerAccumulator 1_719_954_795 1_091_579_898 1_064_728_612 1_583_324_524 8_779_903 1_617_648_793,
    eagerAccumulator 290_055_540 731_497_269 1_296_760_854 70_503_769 686_423_258 208_858_728,
    eagerAccumulator 1_563_210_416 118_534_320 1_545_875_413 1_504_366_916 254_133_068 1_570_337_435,
    eagerAccumulator 823_944_173 1_301_229_134 987_094_534 1_789_450_373 1_850_604_046 1_081_113_244,
    eagerAccumulator 1_180_385_516 669_497_558 1_502_627_924 317_731_699 1_910_146_772 1_893_287_826,
    eagerAccumulator 1_938_766_928 1_960_525_853 1_898_094_493 119_234_826 106_577_691 650_145_580,
    eagerAccumulator 1_195_559_174 1_654_186_273 1_843_983_376 1_810_052_223 485_930_416 1_352_676_922,
    eagerAccumulator 564_306_877 39_122_335 1_101_722_498 718_930_214 360_021_254 1_556_388_575,
    eagerAccumulator 1_693_439_791 1_967_448_769 508_521_483 1_515_305_182 597_835_272 475_511_525,
    eagerAccumulator 1_077_462_604 1_572_608_938 1_787_517_539 1_007_102_925 693_742_175 1_702_580_886,
    eagerAccumulator 1_272_291_992 1_196_529_042 1_380_812_450 1_973_469_016 980_447_405 1_330_034_828,
    eagerAccumulator 52_200_362 1_737_143_511 900_487_722 1_173_435_627 1_285_118_854 514_666_826,
    eagerAccumulator 1_078_562_766 367_545_598 1_936_813_288 1_363_052_213 1_468_580_206 476_472_986,
    eagerAccumulator 48_610_214 1_835_964_488 914_478_223 1_818_831_651 551_482_132 62_704_095,
    eagerAccumulator 409_271_310 1_177_485_674 183_042_175 1_955_489_313 591_808_663 190_976_754,
    eagerAccumulator 1_741_527_227 641_919_040 229_961_289 606_787_982 1_762_939_581 1_355_492_468,
    eagerAccumulator 195_028_523 1_033_379_202 1_295_114_498 1_455_810_171 1_153_756_162 1_425_633_615,
    eagerAccumulator 474_308_669 904_467_356 1_064_621_430 1_466_724_690 1_280_274_089 590_505_955,
    eagerAccumulator 574_348_412 539_898_820 502_234_071 1_080_969_272 618_956_884 33_925_008,
    eagerAccumulator 884_932_441 1_046_750_636 1_405_022_313 54_961_006 398_044_487 446_607_842,
    eagerAccumulator 1_471_999_492 1_346_966_357 968_304_641 903_469_932 621_017_211 984_330_848,
    eagerAccumulator 684_508_276 1_930_807_419 1_658_885_111 1_278_315_527 870_900_047 681_285_391,
    eagerAccumulator 479_917_017 288_737_316 1_992_447_220 1_743_126_645 69_295_315 1_454_578_534,
    eagerAccumulator 346_016_915 124_282_931 719_552_133 1_394_024_920 1_270_560_617 803_085_375,
    eagerAccumulator 174_013_742 69_096_854 811_531_966 297_411_508 386_523_781 1_583_817_155,
    eagerAccumulator 472_556_762 1_495_329_901 117_363_832 1_639_181_664 384_620_433 1_569_967_138,
    eagerAccumulator 1_899_081_717 1_520_781_576 1_012_641_373 1_797_882_604 492_411_830 744_337_861,
    eagerAccumulator 557_950_601 1_222_231_145 1_687_630_310 1_558_079_190 1_222_181_926 1_995_104_775,
    eagerAccumulator 1_119_325_033 1_112_737_729 1_038_533_389 1_699_531_283 1_948_019_221 1_989_563_073,
    eagerAccumulator 840_513_418 341_127_138 1_394_422_547 230_016_907 468_343_951 420_699_881,
    eagerAccumulator 810_604_498 694_147_768 387_107_727 1_355_073_070 1_688_600_928 238_749_533,
    eagerAccumulator 500_104_110 1_347_078_704 235_793_252 1_867_854_751 954_249_670 1_305_182_672,
    eagerAccumulator 1_450_377_785 8_869_670 613_997_721 142_974_156 164_754_037 507_810_444,
    eagerAccumulator 821_335_788 561_497_602 1_150_463_145 253_680_625 1_563_771_601 378_197_105,
    eagerAccumulator 1_895_574_214 1_106_381_175 1_325_603_501 866_974_579 497_076_268 699_554_396,
    eagerAccumulator 834_006_637 714_531_986 722_720_034 345_198_595 1_416_536_249 1_065_597_977,
    eagerAccumulator 388_280_009 1_945_706_739 708_455_314 1_128_209_690 773_327_815 1_576_225_368,
    eagerAccumulator 539_126_558 723_121_644 272_231_606 225_463_844 616_751_384 343_544_554,
    eagerAccumulator 1_709_067_224 1_488_669_103 1_249_534_727 722_830_968 1_043_209_713 265_154_528,
    eagerAccumulator 1_873_789_243 1_444_134_384 1_973_627_528 920_631_253 1_822_823_135 1_267_552_982,
    eagerAccumulator 1_200_575_551 1_301_344_686 1_641_461_638 529_114_380 1_189_108_609 990_374_413,
    eagerAccumulator 1_565_961_980 574_786_263 586_429_900 1_149_806_483 1_889_410_653 620_712_501,
    eagerAccumulator 1_994_113_123 898_827_746 1_270_148_032 1_391_885_593 1_931_934_662 1_197_127_787,
    eagerAccumulator 1_390_881_810 753_468_987 1_184_905_231 424_984_433 233_806_310 743_162_781,
    eagerAccumulator 1_609_389_945 1_870_983_244 867_028_739 1_646_539_585 1_180_276_270 1_723_464_654,
    eagerAccumulator 216_900_023 537_599_585 527_859_524 618_929_962 1_204_070_488 1_073_363_093,
    eagerAccumulator 96_850_916 483_797_571 693_584_846 716_813_256 1_803_435_822 1_755_245_617]

private def checkpointPosition (i : Fin 129) : ℕ :=
  if i.val = 128 then 16383 else 128 * i.val

private def currentIndex (i : Fin 128) : Fin 129 :=
  ⟨i.val, by omega⟩

private def nextIndex (i : Fin 128) : Fin 129 :=
  ⟨i.val + 1, by omega⟩

private def blockStart (i : Fin 128) : ℕ :=
  128 * i.val

private def blockCount (i : Fin 128) : ℕ :=
  if i.val = 127 then 127 else 128

private def blockStop (i : Fin 128) : ℕ :=
  blockStart i + blockCount i

private theorem checkpointPosition_current (i : Fin 128) :
    checkpointPosition (currentIndex i) = blockStart i := by
  unfold checkpointPosition currentIndex blockStart
  rw [if_neg (Nat.ne_of_lt i.isLt)]

private theorem checkpointPosition_next (i : Fin 128) :
    checkpointPosition (nextIndex i) = blockStop i := by
  unfold checkpointPosition nextIndex blockStop blockStart blockCount
  by_cases hlast : i.val = 127
  · simp [hlast]
  · have hnext : i.val + 1 ≠ 128 := by omega
    simp [hlast, hnext, Nat.mul_add]

private theorem blockStop_lt (i : Fin 128) :
    blockStop i < 2 ^ 14 := by
  unfold blockStop blockStart blockCount
  split <;> omega

private def checkpointState (stop : ℕ) (accumulator : EagerModPack) :
    EagerScanState where
  rowSums := GrayPermanentDP.subsetRowSums eagerPackMatrix
    (GrayPermanentDP.grayAt stop)
  totals := KernelPermanentDP.columnTotals eagerPackMatrix
  accumulator := accumulator

private def resumeScan (start count : ℕ) (state : EagerScanState) :
    EagerScanState :=
  (List.range' start count).foldl
    (GrayPermanentDP.step eagerPackMatrix) state

private theorem state_ext {a b : EagerScanState}
    (hrowSums : a.rowSums = b.rowSums)
    (htotals : a.totals = b.totals)
    (haccumulator : a.accumulator = b.accumulator) : a = b := by
  cases a
  cases b
  simp_all

private theorem previous_naturalIndex_succ (n : ℕ)
    (hn : n + 1 < 2 ^ 14) :
    GrayPermanentDP.previousIndex
        (GrayPermanentDP.naturalIndex (n + 1)) =
      GrayPermanentDP.naturalIndex n := by
  apply Fin.ext
  simp only [GrayPermanentDP.previousIndex,
    GrayPermanentDP.naturalIndex, Fin.val_ofNat]
  rw [Nat.mod_eq_of_lt hn]
  rw [Nat.mod_eq_of_lt (show n < 2 ^ 14 by omega)]
  omega

private theorem resumeScan_succ (start count : ℕ)
    (state : EagerScanState) :
    resumeScan start (count + 1) state =
      resumeScan (start + 1) count
        (GrayPermanentDP.step eagerPackMatrix state start) := by
  simp [resumeScan, List.range'_succ]

private theorem resumeScan_rowSums
    (start count : ℕ) (state : EagerScanState)
    (hrowSums : state.rowSums =
      GrayPermanentDP.subsetRowSums eagerPackMatrix
        (GrayPermanentDP.grayAt start))
    (hbound : start + count < 2 ^ 14) :
    (resumeScan start count state).rowSums =
      GrayPermanentDP.subsetRowSums eagerPackMatrix
        (GrayPermanentDP.grayAt (start + count)) := by
  induction count generalizing start state with
  | zero =>
      simpa [resumeScan] using hrowSums
  | succ count ih =>
      rw [resumeScan_succ]
      have hstep :
          (GrayPermanentDP.step eagerPackMatrix state start).rowSums =
            GrayPermanentDP.subsetRowSums eagerPackMatrix
              (GrayPermanentDP.grayAt (start + 1)) := by
        simp only [GrayPermanentDP.step, GrayPermanentDP.advance]
        rw [hrowSums]
        have hupdate :=
          GrayPermanentDP.updateRowSums_eq_subsetRowSums
            eagerPackMatrix (GrayPermanentDP.naturalIndex (start + 1))
        rw [previous_naturalIndex_succ start (by omega)] at hupdate
        simpa only [GrayPermanentDP.grayAt] using hupdate
      have hrec := ih (start := start + 1)
        (state := GrayPermanentDP.step eagerPackMatrix state start)
        hstep (by omega)
      rw [show (start + 1) + count = start + (count + 1) by omega] at hrec
      exact hrec

private theorem resumeScan_totals
    (start count : ℕ) (state : EagerScanState)
    (htotals : state.totals =
      KernelPermanentDP.columnTotals eagerPackMatrix) :
    (resumeScan start count state).totals =
      KernelPermanentDP.columnTotals eagerPackMatrix := by
  induction count generalizing start state with
  | zero =>
      simpa [resumeScan] using htotals
  | succ count ih =>
      rw [resumeScan_succ]
      apply ih
      simpa only [GrayPermanentDP.step, GrayPermanentDP.advance] using
        htotals

private theorem resumeScan_checkpointState_eq
    (i : Fin 128)
    (haccumulator :
      (resumeScan (blockStart i) (blockCount i)
        (checkpointState (blockStart i)
          (checkpointAccumulator (currentIndex i)))).accumulator =
            checkpointAccumulator (nextIndex i)) :
    resumeScan (blockStart i) (blockCount i)
        (checkpointState (blockStart i)
          (checkpointAccumulator (currentIndex i))) =
      checkpointState (blockStop i)
        (checkpointAccumulator (nextIndex i)) := by
  apply state_ext
  · exact resumeScan_rowSums _ _ _ rfl (blockStop_lt i)
  · exact resumeScan_totals _ _ _ rfl
  · exact haccumulator

private theorem resumeScan_append (start first second : ℕ)
    (state : EagerScanState) :
    resumeScan start (first + second) state =
      resumeScan (start + first) second
        (resumeScan start first state) := by
  unfold resumeScan
  rw [← List.range'_append (s := start) (m := first)
    (n := second) (step := 1)]
  simp only [one_mul, List.foldl_append]

private theorem run_eq_resumeScan (stop : ℕ) :
    GrayPermanentDP.run eagerPackMatrix stop =
      resumeScan 0 stop (GrayPermanentDP.initialState eagerPackMatrix) := by
  simp [GrayPermanentDP.run, resumeScan, List.range'_eq_map_range]

private theorem grayAt_zero : GrayPermanentDP.grayAt 0 = 0 := by
  decide +kernel

private theorem initial_rowSums :
    (GrayPermanentDP.initialState eagerPackMatrix).rowSums =
      GrayPermanentDP.subsetRowSums eagerPackMatrix
        (GrayPermanentDP.grayAt 0) := by
  change (KernelPermanentDP.zeroRow :
      KernelPermanentDP.RowValues EagerModPack) =
    GrayPermanentDP.subsetRowSums eagerPackMatrix
      (GrayPermanentDP.grayAt 0)
  rw [grayAt_zero]
  apply Array.ext
  · simp [KernelPermanentDP.zeroRow, GrayPermanentDP.subsetRowSums]
  · intro j hj₁ hj₂
    simp [KernelPermanentDP.zeroRow, GrayPermanentDP.subsetRowSums,
      CyclotomicBitmask.maskSubset]

private theorem initialState_eq_checkpointState :
    GrayPermanentDP.initialState eagerPackMatrix =
      checkpointState 0 (checkpointAccumulator 0) := by
  apply state_ext
  · exact initial_rowSums
  · rfl
  · decide +kernel

private abbrev CheckpointBlockStatement (i : Fin 128) : Prop :=
    (resumeScan (blockStart i) (blockCount i)
      (checkpointState (blockStart i)
        (checkpointAccumulator (currentIndex i)))).accumulator =
      checkpointAccumulator (nextIndex i)

private def groupIndex (group : Fin 8) (offset : Fin 16) : Fin 128 :=
  ⟨16 * group.val + offset.val, by omega⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem checkpointBlock000_015 (offset : Fin 16) :
    CheckpointBlockStatement (groupIndex 0 offset) := by
  fin_cases offset <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem checkpointBlock016_031 (offset : Fin 16) :
    CheckpointBlockStatement (groupIndex 1 offset) := by
  fin_cases offset <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem checkpointBlock032_047 (offset : Fin 16) :
    CheckpointBlockStatement (groupIndex 2 offset) := by
  fin_cases offset <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem checkpointBlock048_063 (offset : Fin 16) :
    CheckpointBlockStatement (groupIndex 3 offset) := by
  fin_cases offset <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem checkpointBlock064_079 (offset : Fin 16) :
    CheckpointBlockStatement (groupIndex 4 offset) := by
  fin_cases offset <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem checkpointBlock080_095 (offset : Fin 16) :
    CheckpointBlockStatement (groupIndex 5 offset) := by
  fin_cases offset <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem checkpointBlock096_111 (offset : Fin 16) :
    CheckpointBlockStatement (groupIndex 6 offset) := by
  fin_cases offset <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem checkpointBlock112_127 (offset : Fin 16) :
    CheckpointBlockStatement (groupIndex 7 offset) := by
  fin_cases offset <;> decide +kernel

private theorem checkpointBlockByGroup (group : Fin 8) (offset : Fin 16) :
    CheckpointBlockStatement (groupIndex group offset) := by
  fin_cases group
  · exact checkpointBlock000_015 offset
  · exact checkpointBlock016_031 offset
  · exact checkpointBlock032_047 offset
  · exact checkpointBlock048_063 offset
  · exact checkpointBlock064_079 offset
  · exact checkpointBlock080_095 offset
  · exact checkpointBlock096_111 offset
  · exact checkpointBlock112_127 offset

private theorem checkpointBlock (i : Fin 128) :
    CheckpointBlockStatement i := by
  let group : Fin 8 :=
    ⟨i.val / 16, by
      apply Nat.div_lt_of_lt_mul
      simp [i.isLt]⟩
  let offset : Fin 16 := ⟨i.val % 16, Nat.mod_lt _ (by norm_num)⟩
  have hdecomp : groupIndex group offset = i := by
    apply Fin.ext
    change 16 * (i.val / 16) + i.val % 16 = i.val
    simpa only [Nat.add_comm] using (Nat.mod_add_div i.val 16)
  rw [← hdecomp]
  exact checkpointBlockByGroup group offset

private theorem checkpointStateBlock (i : Fin 128) :
    resumeScan (blockStart i) (blockCount i)
        (checkpointState (blockStart i)
          (checkpointAccumulator (currentIndex i))) =
      checkpointState (blockStop i)
        (checkpointAccumulator (nextIndex i)) :=
  resumeScan_checkpointState_eq i (checkpointBlock i)

private theorem checkpointChain (k : ℕ) (hk : k ≤ 128) :
    resumeScan 0 (checkpointPosition ⟨k, by omega⟩)
        (checkpointState 0 (checkpointAccumulator 0)) =
      checkpointState (checkpointPosition ⟨k, by omega⟩)
        (checkpointAccumulator ⟨k, by omega⟩) := by
  induction k with
  | zero =>
      simp [checkpointPosition, resumeScan]
  | succ k ih =>
      have hklt : k < 128 := by omega
      let i : Fin 128 := ⟨k, hklt⟩
      have hcurrent := ih (by omega)
      change resumeScan 0 (checkpointPosition (nextIndex i))
          (checkpointState 0 (checkpointAccumulator 0)) =
        checkpointState (checkpointPosition (nextIndex i))
          (checkpointAccumulator (nextIndex i))
      rw [checkpointPosition_next i]
      have hindex : (⟨k, by omega⟩ : Fin 129) = currentIndex i := by
        apply Fin.ext
        rfl
      have hcurrent' :
          resumeScan 0 (blockStart i)
              (checkpointState 0 (checkpointAccumulator 0)) =
            checkpointState (blockStart i)
              (checkpointAccumulator (currentIndex i)) := by
        rw [hindex, checkpointPosition_current i] at hcurrent
        exact hcurrent
      calc
        resumeScan 0 (blockStop i)
            (checkpointState 0 (checkpointAccumulator 0)) =
            resumeScan 0 (blockStart i + blockCount i)
              (checkpointState 0 (checkpointAccumulator 0)) := rfl
        _ = resumeScan (blockStart i) (blockCount i)
              (resumeScan 0 (blockStart i)
                (checkpointState 0 (checkpointAccumulator 0))) :=
          by
            simpa only [Nat.zero_add] using
              resumeScan_append 0 (blockStart i) (blockCount i)
                (checkpointState 0 (checkpointAccumulator 0))
        _ = resumeScan (blockStart i) (blockCount i)
              (checkpointState (blockStart i)
                (checkpointAccumulator (currentIndex i))) := by
          rw [hcurrent']
        _ = checkpointState (blockStop i)
              (checkpointAccumulator (nextIndex i)) :=
          checkpointStateBlock i

private theorem allCheckpointStates :
    resumeScan 0 16383
        (checkpointState 0 (checkpointAccumulator 0)) =
      checkpointState 16383 (checkpointAccumulator ⟨128, by omega⟩) := by
  simpa [checkpointPosition] using checkpointChain 128 (by omega)

set_option maxRecDepth 4096 in
private theorem finalAccumulator_eq_expected :
    checkpointAccumulator ⟨128, by omega⟩ =
      expectedEagerPermanent := by
  rfl

/-- The complete Gray scan has the six independently certified residues. -/
theorem permanentGray_eagerPackMatrix_compact :
    GrayPermanentDP.permanentGray eagerPackMatrix =
      expectedEagerPermanent := by
  unfold GrayPermanentDP.permanentGray
  change (GrayPermanentDP.run eagerPackMatrix 16383).accumulator =
    expectedEagerPermanent
  rw [run_eq_resumeScan, initialState_eq_checkpointState,
    allCheckpointStates]
  simpa only [checkpointState] using finalAccumulator_eq_expected

/-- Unconditional permanent certificate in the strict six-ring product. -/
theorem permanent_eagerPackMatrix_compact :
    Matrix.permanent eagerPackMatrix = expectedEagerPermanent := by
  rw [← GrayPermanentDP.permanentGray_eq_permanent]
  exact permanentGray_eagerPackMatrix_compact

end CyclotomicCertificate
end SunCotangent
