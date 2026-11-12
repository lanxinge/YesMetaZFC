import YesMetaZFC.SetTheory.Boolean.Interval

/-! # 完全布尔同态的主核及忠实限制

先在原模型分离零纤维，再取其内部上确界 k。完全性证明 f(k)=0；
在 ¬k 以下，差 a∧¬b 同时落在 k 与 ¬k 以下，因而必须为零。
-/
namespace YesMetaZFC.SetTheory.BooleanZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
include hZF

theorem Cbh_d.kernel_l {B R z C S w F : M.Domain} (hom : Cbh_d I B R z C S w F)
    (source : Cba_d I B R z) (target : Boolean_d I C S w) :
    ∃ N k u A G,
      (∀ a, M.mem a N ↔ M.mem a B ∧ M.PairMember I a w F) ∧ Bsup_d I B R N k ∧
      M.PairMember I k w F ∧ Imp_d I B R k z u ∧
      (∀ a, M.mem a A ↔ M.mem a B ∧ M.PairMember I a u R) ∧
      M.IsRestrictionOf I G F A ∧ Cba_d I A R z ∧ Cbh_d I A R z C S w G ∧ M.IsSetInjectionFromTo I G A C ∧
      (∀ a, M.mem a B → (M.PairMember I a w F ↔ M.PairMember I a k R)) ∧
      (∀ a b x y, M.PairMember I a x G → M.PairMember I b y G →
        (M.PairMember I x y S ↔ M.PairMember I a b R)) ∧
      ∀ a y, M.PairMember I a y F → ∃ d, M.PairMember I d y G := by
  -- 零纤维在原模型内成集；完全性使其上确界仍在核内，故核恰为 ↓k。
  let ρ : Env M 2 := ⟨Fin.cases F (fun _ => w),fun _ => F⟩
  let φ : UnarySchema 2 := { body := Formula.orderedPairMem 𝒞 .newest (.bound 2) (.bound 1) }
  obtain ⟨N,members⟩ := ZF.separation_exists_d hZF φ ρ B
  have kernel a : M.mem a N ↔ M.mem a B ∧ M.PairMember I a w F :=
    (members a).trans (and_congr_right fun _ => Formula.satisfies_orderedPairMem_iff I ..)
  have sub : M.MemberSubset N B := fun a ha => ((kernel a).mp ha).1
  obtain ⟨k,sup⟩ := source.sup N sub
  obtain ⟨t,ht,kt⟩ := hom.function.2.2 k sup.1
  have below := (hom.sup N k t sub sup kt).2 w target.bot_mem (by
    intro a y ha ay
    have eq := hom.function.1.2 a y w ay ((kernel a).mp ha).2
    exact eq ▸ target.order.refl w target.bot_mem)
  have eq := target.order.antisymm t w ht target.bot_mem below (target.bot_le t ht)
  have zero : M.PairMember I k w F := eq ▸ kt
  have principal a (ha : M.mem a B) : M.PairMember I a w F ↔ M.PairMember I a k R := by
    constructor
    · intro aw; exact sup.2.1 a ((kernel a).mpr ⟨ha,aw⟩)
    · intro ak
      obtain ⟨x,hx,ax⟩ := hom.function.2.2 a ha
      have eq := target.order.antisymm x w hx target.bot_mem
        (hom.toBh_d.mono_l I source.toBoolean_d target ax zero ak) (target.bot_le x hx)
      exact eq ▸ ax
  obtain ⟨u,neg⟩ := source.imp k z sup.1 source.bot_mem
  let η : Env M 2 := ⟨Fin.cases R (fun _ => u),fun _ => R⟩
  let ψ : UnarySchema 2 := { body := Formula.orderedPairMem 𝒞 .newest (.bound 2) (.bound 1) }
  obtain ⟨A,carrier⟩ := ZF.separation_exists_d hZF ψ η B
  have domain a : M.mem a A ↔ M.mem a B ∧ M.PairMember I a u R :=
    (carrier a).trans (and_congr_right fun _ => Formula.satisfies_orderedPairMem_iff I ..)
  have interval : Bi_d I B R u A := ⟨neg.1,domain⟩
  have algebra := interval.complete_l I source
  obtain ⟨G,cut⟩ := ZF.exists_restriction hZF I F A
  have fn := cut.isSetFunctionFromTo hom.function (fun a ha => ((domain a).mp ha).1)
  obtain ⟨v,hv,uv⟩ := hom.function.2.2 u neg.1
  have top := hom.neg k u w v zero uv neg
  have isTop y (hy : M.mem y C) : M.PairMember I y v S :=
    (top.adjoint_l I target.order hy (meet_comm_d I
      (meet_of_le_l I target.order target.bot_mem hy (target.bot_le y hy)))).mpr
        (target.order.refl w target.bot_mem)
  -- 主区间中的补为 u∧¬a，上确界与原代数一致，故实际限制图仍为完全同态。
  have reduced : Cbh_d I A R z C S w G := by
    refine ⟨⟨fn,(cut.2 z w).mpr ⟨algebra.bot_mem,hom.zero⟩,?_,?_⟩,?_⟩
    · intro a b c a' b' c' aa bb cc meet
      exact hom.meet a b c a' b' c' ((cut.2 a a').mp aa).2 ((cut.2 b b').mp bb).2
        ((cut.2 c c').mp cc).2 ((interval.meet_l I source.toBoolean_d
          (fn.input_mem_of_pairMember aa) (fn.input_mem_of_pairMember bb)).mp meet)
    · intro a n a' n' aa nn relative
      have ha := fn.input_mem_of_pairMember aa
      have aa := ((cut.2 a a').mp aa).2
      have nn := ((cut.2 n n').mp nn).2
      obtain ⟨m,hm⟩ := source.imp a z ((domain a).mp ha).1 source.bot_mem
      obtain ⟨t,ht⟩ := source.meet u m neg.1 hm.1
      have eq := (interval.imp_l I source.toBoolean_d ha hm ht).unique_l I algebra.order relative
      have ht : Meet_d I B R u m n := eq ▸ ht
      obtain ⟨m',hm',mm⟩ := hom.function.2.2 m hm.1
      have eq := (hom.meet u m n v m' n' uv mm nn ht).unique_l I target.order
        (meet_comm_d I (meet_of_le_l I target.order hm' hv (isTop m' hm')))
      exact eq.symm ▸ hom.neg a m a' m' aa mm hm
    · intro D a a' sub sup aa
      have mapped := hom.sup D a a' (fun x hx => ((domain x).mp (sub x hx)).1)
        ((interval.sup_l I source.toBoolean_d sub).mp sup) ((cut.2 a a').mp aa).2
      exact ⟨fun x y hx xy => mapped.1 x y hx ((cut.2 x y).mp xy).2,
        fun d hd bound => mapped.2 d hd (fun x y hx xy => bound x y hx ((cut.2 x y).mpr ⟨sub x hx,xy⟩))⟩
  -- 若 f(a)≤f(b)，则 a∧¬b 同时在 k 与 ¬k 以下，因而为零。
  have reflects a b x y (ax : M.PairMember I a x G) (bb : M.PairMember I b y G)
      (xy : M.PairMember I x y S) : M.PairMember I a b R := by
    have ha := (domain a).mp (fn.input_mem_of_pairMember ax)
    have hb := (domain b).mp (fn.input_mem_of_pairMember bb)
    have ax := ((cut.2 a x).mp ax).2
    have bb := ((cut.2 b y).mp bb).2
    obtain ⟨n,hn⟩ := source.imp b z hb.1 source.bot_mem
    obtain ⟨m,meet⟩ := source.meet a n ha.1 hn.1
    obtain ⟨n',_,nn⟩ := hom.function.2.2 n hn.1
    obtain ⟨m',_,mm⟩ := hom.function.2.2 m meet.1
    have eq := (target.neg_test_l I (hom.function.output_mem_of_pairMember ax)
      (hom.function.output_mem_of_pairMember bb) (hom.neg b n y n' bb nn hn)
      (hom.meet a n m x n' m' ax nn mm meet)).mp xy
    have mk := (principal m meet.1).mp (eq ▸ mm)
    have mu := source.order.trans m a u meet.1 ha.1 neg.1 (meet_bounds_d I source.order meet).1 ha.2
    exact (source.toBoolean_d.neg_test_l I ha.1 hb.1 hn meet).mpr
      (source.toBoolean_d.disjoint_l I sup.1 meet.1 neg mk mu)
  have injective : M.IsSetInjectionFromTo I G A C := ⟨fn,fun a b y ay bb =>
    source.order.antisymm a b ((domain a).mp (fn.input_mem_of_pairMember ay)).1
      ((domain b).mp (fn.input_mem_of_pairMember bb)).1
      (reflects a b y y ay bb (target.order.refl y (fn.output_mem_of_pairMember ay)))
      (reflects b a y y bb ay (target.order.refl y (fn.output_mem_of_pairMember ay)))⟩
  refine ⟨N,k,u,A,G,kernel,sup,zero,neg,domain,cut,algebra,reduced,injective,principal,?_,?_⟩
  · intro a b x y ax bb
    exact ⟨reflects a b x y ax bb,hom.toBh_d.mono_l I source.toBoolean_d target
      ((cut.2 a x).mp ax).2 ((cut.2 b y).mp bb).2⟩
  · intro a y ay
    -- f(a∧u)=f(a)，所以限制没有损失原图的任何像值。
    have ha := hom.function.input_mem_of_pairMember ay
    obtain ⟨d,meet⟩ := source.meet a u ha neg.1
    obtain ⟨d',_,dd⟩ := hom.function.2.2 d meet.1
    have same := (hom.meet a u d y v d' ay uv dd meet).unique_l I target.order
      (meet_of_le_l I target.order (hom.function.output_mem_of_pairMember ay) hv (isTop y (hom.function.output_mem_of_pairMember ay)))
    exact ⟨d,(cut.2 d y).mpr ⟨(domain d).mpr ⟨meet.1,(meet_bounds_d I source.order meet).2⟩,same ▸ dd⟩⟩

end YesMetaZFC.SetTheory.BooleanZF
