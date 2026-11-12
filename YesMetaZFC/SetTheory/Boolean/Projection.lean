import YesMetaZFC.SetTheory.Boolean.Interval

/-! # 相交到主区间的实际完全同态

一次用替换构造 a↦a∧u 的集合图。任意内部上确界的保持由剩余的伴随律推出，
无需选择运算函数，也无需对族的大小作额外限制。
-/
namespace YesMetaZFC.SetTheory.BooleanZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
include hZF

theorem Bi_d.project_l {B R z u A : M.Domain} (interval : Bi_d I B R u A)
    (source : Boolean_d I B R z) : ∃ F, Cbh_d I B R z A R z F ∧
      ∀ a c, M.PairMember I a c F ↔ M.mem a B ∧ Meet_d I B R a u c := by
  let ρ : Env M 3 := ⟨fun i => [B,R,u].get i,fun _ => B⟩
  let φ : BinarySchema 3 := { body := meet_m 𝒞 (.bound 2) (.bound 3) (.bound 1) (.bound 4) .newest }
  have sat a c : φ.denote ρ a c ↔ Meet_d I B R a u c := meet_sat_d I ..
  obtain ⟨F,fn,values⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := B) (target := A)
    (fun a ha => (source.meet a u ha interval.bound).imp fun c hc => (sat a c).mpr hc)
    (fun a _ c d hc hd => ((sat a c).mp hc).unique_l I source.order ((sat a d).mp hd))
    (fun a c _ hc => (interval.carrier c).mpr ⟨((sat a c).mp hc).1,
      (meet_bounds_d I source.order ((sat a c).mp hc)).2⟩)
  have graph a c : M.PairMember I a c F ↔ M.mem a B ∧ Meet_d I B R a u c :=
    (values a c).trans (and_congr_right fun _ => sat a c)
  have algebra := interval.boolean_l I source
  refine ⟨F,⟨⟨fn,(graph z z).mpr ⟨source.bot_mem,meet_of_le_l I source.order source.bot_mem interval.bound
    (source.bot_le u interval.bound)⟩,?_,?_⟩,?_⟩,graph⟩
  · intro a b c a' b' c' aa bb cc meet
    have ma := ((graph a a').mp aa).2
    have mb := ((graph b b').mp bb).2
    have mc := ((graph c c').mp cc).2
    apply (interval.meet_l I source (fn.output_mem_of_pairMember aa) (fn.output_mem_of_pairMember bb)).mpr
    refine ⟨mc.1,fun d hd => ?_⟩
    rw [mc.2 d hd,meet.2 d hd,ma.2 d hd,mb.2 d hd]
    exact ⟨fun ⟨⟨da,db⟩,du⟩ => ⟨⟨da,du⟩,⟨db,du⟩⟩,fun ⟨⟨da,du⟩,⟨db,_⟩⟩ => ⟨⟨da,db⟩,du⟩⟩
  · intro a n a' n' aa nn neg
    have ha := fn.input_mem_of_pairMember aa
    have ha' := fn.output_mem_of_pairMember aa
    have ma := ((graph a a').mp aa).2
    have mn := ((graph n n').mp nn).2
    have forward {d m} (hd : M.mem d A) (meet : Meet_d I B R d a m) : Meet_d I A R d a' m := by
      apply (interval.meet_l I source hd ha').mpr
      refine ⟨meet.1,fun x hx => (meet.2 x hx).trans ?_⟩
      exact ⟨fun ⟨xd,xa⟩ => ⟨xd,(ma.2 x hx).mpr ⟨xa,source.order.trans x d u hx
        ((interval.carrier d).mp hd).1 interval.bound xd ((interval.carrier d).mp hd).2⟩⟩,
        fun ⟨xd,xa⟩ => ⟨xd,((ma.2 x hx).mp xa).1⟩⟩
    refine ⟨fn.output_mem_of_pairMember nn,fun d hd => ?_⟩
    have bound := (interval.carrier d).mp hd
    apply (mn.2 d bound.1).trans
    apply (show (M.PairMember I d n R ∧ M.PairMember I d u R) ↔ M.PairMember I d n R from
      ⟨And.left,fun dn => ⟨dn,bound.2⟩⟩).trans
    apply (neg.2 d bound.1).trans
    constructor
    · intro all m meet
      obtain ⟨t,ht⟩ := source.meet d a bound.1 ha
      exact (forward hd ht).unique_l I algebra.order meet ▸ all t ht
    · intro all m meet
      exact all m (forward hd meet)
  · intro D a a' sub sup aa
    have ma := ((graph a a').mp aa).2
    constructor
    · intro x y hx xy
      exact (((graph x y).mp xy).2).mono_l I source.order (sub x hx) interval.bound sup.1 interval.bound
        ma (sup.2.1 x hx) (source.order.refl u interval.bound)
    · intro d hd upper
      obtain ⟨i,imp⟩ := source.imp u d interval.bound ((interval.carrier d).mp hd).1
      apply (imp.adjoint_l I source.order sup.1 ma).mp
      apply sup.2.2 i imp.1
      intro x hx
      obtain ⟨y,_,xy⟩ := fn.2.2 x (sub x hx)
      exact (imp.adjoint_l I source.order (sub x hx) ((graph x y).mp xy).2).mpr (upper x y hx xy)

end YesMetaZFC.SetTheory.BooleanZF
