import YesMetaZFC.Model.SetTheory.Embedding.PredicateTrace
import YesMetaZFC.SetTheory.Filter.Relative
import YesMetaZFC.SetTheory.Filter.Source
import YesMetaZFC.Model.SetTheory.ReducedPower.SourceModel
import YesMetaZFC.Model.SetTheory.ReducedPower.Restriction
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationNormalize

/-! # 从实际初等嵌入派生内部超滤

对 a∈j(D)，先在源中指定的子集代数上分离 U={s : a∈j(s)}。
子集、空集、交和相对补的保持给出相对超滤；完整幂集作为其实例恢复极大滤子。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Ed_trace_d (j a B U : M.Domain) : Prop := ∀ s, M.mem s U ↔
  M.mem s B ∧ ∃ t, M.PairMember I s t j ∧ M.mem a t

def ed_trace_m {d} (j a B U : Term d) : Formula 1 d := .forallE (.iff (.mem .newest U.weaken)
  (.conj (.mem .newest B.weaken) (.existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest j.weaken.weaken) (.mem a.weaken.weaken .newest)))))
derive_free_closed ed_trace_m

theorem ed_trace_sat_l {d} (ρ : Env M d) (j a B U : Term d) :
    Formula.satisfies ρ (ed_trace_m (𝒞 := 𝒞) j a B U) ↔
      Ed_trace_d I (j.eval ρ) (a.eval ρ) (B.eval ρ) (U.eval ρ) := by
  simp only [ed_trace_m, Ed_trace_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]
  rfl

theorem ed_trace_exists_l (hZF : M.Models ZF) (j a B : M.Domain) : ∃ U, Ed_trace_d I j a B U := by
  let ρ : Env M 2 := ⟨Fin.cases j (fun _ => a), fun _ => a⟩
  let φ : UnarySchema 2 := { body := .existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2)) (.mem (.bound 3) .newest)) }
  obtain ⟨U, hU⟩ := ZF.separation_exists_d hZF φ ρ B
  refine ⟨U, fun s => (hU s).trans (and_congr_right fun _ => ?_)⟩
  simp only [φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff]
  rfl

def Ed_filter_d (j a D U : M.Domain) : Prop := ∀ s, M.mem s U ↔
  M.MemberSubset s D ∧ ∃ t, M.PairMember I s t j ∧ M.mem a t

def ed_filter_m {d} (j a D U : Term d) : Formula 1 d :=
  .forallE (.iff (.mem .newest U.weaken) (.conj (Formula.subset .newest D.weaken)
    (.existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest j.weaken.weaken)
      (.mem a.weaken.weaken .newest)))))
derive_free_closed ed_filter_m

theorem ed_filter_sat_l {d} (ρ : Env M d) (j a D U : Term d) :
    Formula.satisfies ρ (ed_filter_m (𝒞 := 𝒞) j a D U) ↔
      Ed_filter_d I (j.eval ρ) (a.eval ρ) (D.eval ρ) (U.eval ρ) := by
  simp only [ed_filter_m, Ed_filter_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]
  rfl

theorem ed_filter_exists_l (hZF : M.Models ZF) (j a D : M.Domain) : ∃ U, Ed_filter_d I j a D U := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF D
  obtain ⟨U, hU⟩ := ed_trace_exists_l I hZF j a P
  exact ⟨U, fun s => (hU s).trans (and_congr (hP s) Iff.rfl)⟩

theorem ed_filter_unique_l (hE : Extensional M) {j a D U V} (hU : Ed_filter_d I j a D U)
    (hV : Ed_filter_d I j a D V) : U = V := hE.eq_of_same_members U V (fun s => (hU s).trans (hV s).symm)

theorem ed_filter_member_l {j a D U s t} (hj : M.IsSetFunction I j) (hU : Ed_filter_d I j a D U)
    (hs : M.MemberSubset s D) (ht : M.PairMember I s t j) : M.mem s U ↔ M.mem a t := by
  rw [hU s]
  exact ⟨fun ⟨_, z, hz, haz⟩ => hj.2 s z t hz ht ▸ haz, fun hat => ⟨hs, t, ht, hat⟩⟩

variable (hZF : M.Models ZF) {ω X A Y B j : M.Domain} (hω : M.IsOmega ω)
  (h : Spred_emb_d I ω X A Y B j) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)

include hZF hω h hX hY

theorem ed_member_l {s s' t t'} (hs : M.PairMember I s s' j) (ht : M.PairMember I t t' j) :
    M.mem s t ↔ M.mem s' t' := by
  have tr := spred_delta_l I hZF hω h hX hY (n := 2) (.mem (.bound 1) (.bound 0))
    (by simp [Definitional.Formula.FreeClosed]) (.mem _ _)
    ⟨Fin.cases t (fun _ => s), fun _ => s⟩ ⟨Fin.cases t' (fun _ => s'), fun _ => s'⟩ (Fin.cases ht (fun _ => hs))
  simp only [Formula.satisfies_mem_iff] at tr
  exact tr

theorem ed_subset_l {s s' t t'} (hs : M.PairMember I s s' j) (ht : M.PairMember I t t' j) :
    M.MemberSubset s t ↔ M.MemberSubset s' t' := by
  have tr := spred_delta_l I hZF hω h hX hY (n := 2) (Formula.subset (.bound 1) (.bound 0))
    (by simp) (.atom _ _ _)
    ⟨Fin.cases t (fun _ => s), fun _ => s⟩ ⟨Fin.cases t' (fun _ => s'), fun _ => s'⟩ (Fin.cases ht (fun _ => hs))
  simp only [Formula.satisfies_subset_iff] at tr
  exact tr

theorem ed_empty_l {s s'} (hs : M.PairMember I s s' j) :
    (∀ x, ¬ M.mem x s) ↔ ∀ x, ¬ M.mem x s' := by
  have tr := spred_delta_l I hZF hω h hX hY (n := 1) (Formula.forallMem (.bound 0) .falsum)
    (by simp [Definitional.Formula.FreeClosed]) (.forallMem _ .falsum)
    ⟨fun _ => s, fun _ => s⟩ ⟨fun _ => s', fun _ => s'⟩ (fun _ => hs)
  simpa only [Formula.satisfies_forallMem_iff, Formula.satisfies_falsum_iff, Definitional.Term.eval] using tr

/-- 在实际定义域上同时保持交与相对补的成员方程。 -/
theorem ed_boolean_l (p : Bool) {D D' s s' t t' r r'}
    (hD : M.PairMember I D D' j) (hs : M.PairMember I s s' j)
    (ht : M.PairMember I t t' j) (hr : M.PairMember I r r' j) :
    (∀ x, M.mem x D → (M.mem x r ↔ M.mem x s ∧ if p then M.mem x t else ¬ M.mem x t)) ↔
    (∀ x, M.mem x D' → (M.mem x r' ↔ M.mem x s' ∧ if p then M.mem x t' else ¬ M.mem x t')) := by
  let φ : Formula 1 4 := Formula.forallMem (.bound 3) (.iff (.mem .newest (.bound 1))
    (.conj (.mem .newest (.bound 3)) (if p then .mem .newest (.bound 2) else .neg (.mem .newest (.bound 2)))))
  have hf : φ.FreeClosed := by cases p <;> simp [φ, Definitional.Formula.FreeClosed]
  have hd : φ.IsDelta0 := by
    cases p
    · exact .forallMem _ (.iff (.mem _ _) (.conj (.mem _ _) (.neg (.mem _ _))))
    · exact .forallMem _ (.iff (.mem _ _) (.conj (.mem _ _) (.mem _ _)))
  have tr := spred_delta_l I hZF hω h hX hY φ hf hd
    ⟨Fin.cases r (Fin.cases t (Fin.cases s (fun _ => D))), fun _ => D⟩
    ⟨Fin.cases r' (Fin.cases t' (Fin.cases s' (fun _ => D'))), fun _ => D'⟩
    (Fin.cases hr (Fin.cases ht (Fin.cases hs (fun _ => hD))))
  cases p <;> simp only [φ, Bool.false_eq_true, ↓reduceIte, Formula.satisfies_forallMem_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_neg_iff,
    Definitional.Term.eval_newest] at tr ⊢ <;> exact tr

/-- 源中实际容许子集代数上的派生超滤；不要求完整背景幂集在源中。 -/
theorem ed_trace_ultrafilter_l {D P D' a : M.Domain} (hP : FilterZF.Field_d D P) (hPX : M.MemberSubset P X)
    (hD : M.PairMember I D D' j) (ha : M.mem a D') :
    ∃ U, Ed_trace_d I j a P U ∧ FilterZF.Rel_ultra_d D P U := by
  obtain ⟨U, hU⟩ := ed_trace_exists_l I hZF j a P
  obtain ⟨c, R, d, S, hx, hy, hj⟩ := h
  have h : Spred_emb_d I ω X A Y B j := ⟨c, R, d, S, hx, hy, hj⟩
  have image {s} (hs : M.mem s P) : ∃ t, M.PairMember I s t j := by
    obtain ⟨t, _, ht⟩ := hj.1.1.2.2 s (hPX s hs)
    exact ⟨t, ht⟩
  have member {s t} (hs : M.mem s P) (ht : M.PairMember I s t j) : M.mem s U ↔ M.mem a t := by
    rw [hU s]
    exact ⟨fun ⟨_, v, hv, hav⟩ => hj.1.1.1.2 s v t hv ht ▸ hav, fun hat => ⟨hs, t, ht, hat⟩⟩
  refine ⟨U, hU, ⟨hP, ⟨fun s hs => hP.bounds s ((hU s).mp hs).1,
    (hU D).mpr ⟨hP.top, D', hD, ha⟩, ?_⟩, fun s hs => ((hU s).mp hs).1, ?_, ?_, ?_⟩⟩
  · intro s t hs ht
    obtain ⟨hsP, s', hs', has⟩ := (hU s).mp hs
    obtain ⟨htP, t', ht', hat⟩ := (hU t).mp ht
    obtain ⟨r, hrP, hr⟩ := hP.inter s t hsP htP
    obtain ⟨r', hr'⟩ := image hrP
    have hb := (ed_boolean_l I hZF hω h hX hY true hD hs' ht' hr').mp (fun x _ => hr x)
    exact ⟨r, (member hrP hr').mpr ((hb a ha).mpr ⟨has, hat⟩),
      fun x hx => ((hr x).mp hx).1, fun x hx => ((hr x).mp hx).2⟩
  · intro s t hs ht hst
    obtain ⟨_, s', hs', has⟩ := (hU s).mp hs
    obtain ⟨t', ht'⟩ := image ht
    exact (member ht ht').mpr ((ed_subset_l I hZF hω h hX hY hs' ht').mp hst a has)
  · intro s hs
    obtain ⟨_, t, ht, hat⟩ := (hU s).mp hs
    apply Classical.byContradiction
    intro hn
    exact (ed_empty_l I hZF hω h hX hY ht).mp (fun x hx => hn ⟨x, hx⟩) a hat
  · intro s t hs ht hc
    obtain ⟨s', hs'⟩ := image hs
    obtain ⟨t', ht'⟩ := image ht
    have hb := (ed_boolean_l I hZF hω h hX hY false hD hD hs' ht').mp (fun x _ => hc x)
    by_cases has : M.mem a s'
    · exact Or.inl ((member hs hs').mpr has)
    · exact Or.inr ((member ht ht').mpr ((hb a ha).mpr ⟨ha, has⟩))

/-- 完整幂集实例直接使用相对构造，原极大滤子接口保持其数学结论。 -/
theorem ed_ultrafilter_l {D P D' a : M.Domain} (hP : M.IsPowerSetOf P D) (hPX : M.mem P X)
    (hD : M.PairMember I D D' j) (ha : M.mem a D') :
    ∃ U, Ed_filter_d I j a D U ∧ FilterZF.Maximal_d (ℳ := M) D U := by
  obtain ⟨U, ht, hu⟩ := ed_trace_ultrafilter_l I hZF hω h hX hY
    (FilterZF.field_power_l (ZF.modelsKP hZF) hP) (hX P hPX) hD ha
  exact ⟨U, fun s => (ht s).trans (and_congr (hP s) Iff.rfl), hu.full_l (ZF.modelsKP hZF) hP⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 派生测度的有界真值集合

在源中实际分离真值集合；其测度值恰等于像公式在种子处的真值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ed_separate_delta_l (hZF : M.Models ZF) {ω X C Y E j D D' P a U}
    (hω : M.IsOmega ω) (h : Spred_emb_d I ω X C Y E j) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hP : M.IsPowerSetOf P D) (hPX : M.MemberSubset P X) (hjD : M.PairMember I D D' j) (ha : M.mem a D')
    (hU : Ed_filter_d I j a D U) {n} (φ : Delta0UnarySchema n) (ρ η : Env M n)
    (hp : ∀ i, M.PairMember I (ρ.bound i) (η.bound i) j) : ∃ A, M.mem A X ∧
      (∀ s, M.mem s A ↔ M.mem s D ∧ φ.toUnarySchema.denote ρ s) ∧
      (M.mem A U ↔ φ.toUnarySchema.denote η a) := by
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  obtain ⟨A, hs⟩ := ZF.separation_exists_d hZF φ.toUnarySchema ρ D
  have hAD : M.MemberSubset A D := fun s ht => ((hs s).mp ht).1
  have hAX := hPX A ((hP A).mpr hAD)
  obtain ⟨A', _, hjA⟩ := hj.2.2 A hAX
  let e : Fin (n + 1) → Fin (n + 3) := Fin.cases 0 (fun i => ⟨i.val + 3, by omega⟩)
  let ψ : Formula 1 (n + 2) := Formula.forallMem .newest
    (.iff (.mem .newest (.bound 2)) (φ.body.rename e))
  have eq (ρ : Env M n) A D s : (((ρ.push A).push D).push s).reindex e = ρ.push s := by
    rw [Env.mk.injEq]
    exact ⟨funext (Fin.cases rfl (fun _ => rfl)), rfl⟩
  have sat (ρ : Env M n) A D : Formula.satisfies ((ρ.push A).push D) ψ ↔
      ∀ s, M.mem s D → (M.mem s A ↔ φ.toUnarySchema.denote ρ s) := by
    simp only [ψ, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_rename, eq]; rfl
  have tr := spred_delta_l I hZF hω h hX hY ψ
    (by simp -implicitDefEqProofs [ψ, Definitional.Formula.FreeClosed, φ.freeClosed])
    (.forallMem _ (.iff (.mem _ _) (φ.delta0.rename_l e))) ((ρ.push A).push D) ((η.push A').push D')
    (Fin.cases hjD (Fin.cases hjA hp))
  have read := (sat η A' D').mp (tr.mp ((sat ρ A D).mpr fun s hd => (hs s).trans
    ⟨And.right, fun hh => ⟨hd, hh⟩⟩)) a ha
  exact ⟨A, hAX, hs, (ed_filter_member_l I hj.1 hU hAD hjA).trans read⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 源内部子集与源内部函数上的实际分量

容许子集恰好是 X 中 D 的子集，代表函数也明确限制为 X 的成员。
源中常值图保证代表族非空，商只消费已经证明的共同细化性质。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ed_source_ultrafilter_l (hZF : M.Models ZF) {ω X A Y B j D D' a}
    (hω : M.IsOmega ω) (h : Spred_emb_d I ω X A Y B j) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hc : Rd_closed_d X) (hD : M.PairMember I D D' j) (ha : M.mem a D') :
    ∃ P U, FilterZF.Source_d X D P ∧ Ed_filter_d I j a D U ∧ FilterZF.Rel_ultra_d D P U := by
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  obtain ⟨P, hP, hp⟩ := FilterZF.source_field_exists_l (ZF.modelsKP hZF) hc (hj.input_mem_of_pairMember hD)
  obtain ⟨U, hu, hf⟩ := ed_trace_ultrafilter_l I hZF hω h hX hY hp (fun s hs => ((hP s).mp hs).1) hD ha
  refine ⟨P, U, hP, fun s => (hu s).trans ?_, hf⟩
  exact ⟨fun ⟨hs, ht⟩ => ⟨((hP s).mp hs).2, ht⟩,
    fun ⟨hs, t, ht, hat⟩ => ⟨(hP s).mpr ⟨hj.input_mem_of_pairMember ht, hs⟩, t, ht, hat⟩⟩

theorem ed_source_model_l (hZF : M.Models ZF) {ω X A Y B j D D' a}
    (hω : M.IsOmega ω) (h : Spred_emb_d I ω X A Y B j) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hc : Rd_closed_d X) (hD : M.PairMember I D D' j) (ha : M.mem a D') : ∃ P U s R G c p C T,
      FilterZF.Source_d X D P ∧ Ed_filter_d I j a D U ∧ FilterZF.Rel_ultra_d D P U ∧
      Smdl_d I s X R ∧ (∀ x y, M.PairMember I x y R ↔ M.mem x X ∧ M.mem y X ∧ M.mem x y) ∧
      (∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d D X f) ∧ Rp_model_d I D X U R c G p C T := by
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  have hDX := hj.input_mem_of_pairMember hD
  obtain ⟨P, U, hP, hu, hU⟩ := ed_source_ultrafilter_l I hZF hω h hX hY hc hD ha
  obtain ⟨s, R, hs, hR⟩ := smdl_membership_l I hZF ⟨D, hDX⟩
  obtain ⟨f, hfX, hf⟩ := FilterZF.source_function_l (ZF.modelsKP hZF) hc hDX
  obtain ⟨G, c, p, C, T, hG, hm⟩ := rp_family_model_l I hZF hU.base hfX hf R
  exact ⟨P, U, s, R, G, c, p, C, T, hP, hu, hU, hs, hR, hG, hm⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 派生测度上的原嵌入求值

求值始终只对已经属于源的函数图定义。精确原子真值集的像在种子处读取，
从而同时识别商的等号及成员关系。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}}

def Ee_value_d (j a f y : M.Domain) : Prop := ∃ g, Rd_entry_d f g j ∧ Rd_entry_d a y g

def ee_value_m {d} (j a f y : Term d) : Formula 1 d := .existsE
  (.conj (rd_entry_m f.weaken .newest j.weaken) (rd_entry_m a.weaken y.weaken .newest))
derive_free_closed ee_value_m

theorem ee_value_sat_l (hE : Extensional M) {d} (ρ : Env M d) (j a f y : Term d) :
    Formula.satisfies ρ (ee_value_m j a f y) ↔ Ee_value_d (j.eval ρ) (a.eval ρ) (f.eval ρ) (y.eval ρ) := by
  simp only [ee_value_m, Ee_value_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem ed_evaluation_l (hZF : M.Models ZF) {ω X A Y B j D D' a f : M.Domain}
    (hω : M.IsOmega ω) (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X A Y B j)
    (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y) (hD : Rd_entry_d D D' j) (ha : M.mem a D')
    (hf : Sfun_d X D f) : ∃ y, M.mem y Y ∧ Ee_value_d j a f y ∧ ∀ z, Ee_value_d j a f z → z = y := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, e⟩ := h; exact e.1.1
  obtain ⟨hfX, C, hCX, hFC⟩ := hf
  obtain ⟨C', hCY, hjC⟩ := hj.2.2 C hCX
  obtain ⟨f', _, hjf⟩ := hj.2.2 f hfX
  have fun' := (spred_function_l I hZF hω h hX hY hD hjC hjf).mp hFC
  obtain ⟨y, hy, hay⟩ := fun'.2.1 a ha
  refine ⟨y, hY C' hCY y hy, ⟨f', hjf, hay⟩, fun z ⟨g, hjg, haz⟩ => ?_⟩
  have eq := hj.1.2 f g f' hjg hjf
  exact (fn0_function_l (ZF.modelsKP hZF) fun').1.2 a z y (eq ▸ haz) hay

/-- 一个源常值函数的任何合法像求值，恰为原常值的像。 -/
theorem ed_constant_value_l (hZF : M.Models ZF) {ω X A Y B j D a f x y z : M.Domain}
    (hω : M.IsOmega ω) (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X A Y B j)
    (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y) (hD : M.mem D X) (hf : Sfun_d X D f)
    (hs : Rs_const_d D x f) (hx : Rd_entry_d x z j) (hy : Ee_value_d j a f y) : y = z := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, e⟩ := h; exact e.1.1
  obtain ⟨_, C, hCX, hFC⟩ := hf
  obtain ⟨D', _, hjD⟩ := hj.2.2 D hD
  obtain ⟨C', _, hjC⟩ := hj.2.2 C hCX
  obtain ⟨f', hjf, haf⟩ := hy
  have ff := (spred_function_l I hZF hω h hX hY hjD hjC hjf).mp hFC
  let φ : Formula 1 3 := Formula.forallMem (.bound 2) (rd_entry0_m .newest (.bound 2) (.bound 1))
  have tr := spred_delta_l I hZF hω h hX hY φ (by simp -implicitDefEqProofs [φ])
    (.forallMem _ (rd_entry0_delta_l ..)) ⟨Fin.cases f (Fin.cases x (fun _ => D)), fun _ => D⟩
    ⟨Fin.cases f' (Fin.cases z (fun _ => D')), fun _ => D'⟩ (Fin.cases hjf (Fin.cases hx (fun _ => hjD)))
  simp only [φ, Formula.satisfies_forallMem_iff, rd_entry0_sat_l hZF.1] at tr
  exact (fn0_function_l (ZF.modelsKP hZF) ff).1.2 a y z haf (tr.mp hs a (ff.bound_l haf).1)

theorem ed_evaluation_atoms_l (hZF : M.Models ZF) {ω X A Y B j D D' a U P c R f g y z : M.Domain}
    (hω : M.IsOmega ω) (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X A Y B j)
    (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y) (hD : Rd_entry_d D D' j) (ha : M.mem a D')
    (hP : M.IsPowerSetOf P D) (hPX : M.MemberSubset P X) (hU : Ed_filter_d (kp_pair_l (ZF.modelsKP hZF)) j a D U)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (hf : Sfun_d X D f) (hg : Sfun_d X D g) (hy : Ee_value_d j a f y) (hz : Ee_value_d j a g z) :
    (Rp_eq_d X U f g ↔ y = z) ∧ (Rp_rel_d (kp_pair_l (ZF.modelsKP hZF)) X U R f g ↔ M.mem y z) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, e⟩ := h; exact e.1.1
  obtain ⟨hfX, C, hCX, hFC⟩ := hf
  obtain ⟨hgX, E, hEX, hGE⟩ := hg
  obtain ⟨C', _, hjC⟩ := hj.2.2 C hCX
  obtain ⟨E', _, hjE⟩ := hj.2.2 E hEX
  obtain ⟨f', hjf, haf⟩ := hy
  obtain ⟨g', hjg, hag⟩ := hz
  have ff := (spred_function_l I hZF hω h hX hY hD hjC hjf).mp hFC
  have gg := (spred_function_l I hZF hω h hX hY hD hjE hjg).mp hGE
  have atom (b : Bool) :
      (∃ V, M.mem V U ∧ ∀ v, M.mem v V → Rp_atom_d I b X R f g v) ↔ (if b then y = z else M.mem y z) := by
    let φ : Delta0UnarySchema 4 := {
      body := Formula.existsMem (.bound 4) (Formula.existsMem (.bound 4)
        (.conj (rd_entry0_m (.bound 2) (.bound 1) (.bound 4)) (.conj (rd_entry0_m (.bound 2) .newest (.bound 3))
          (if b then Formula.extensionalEq (.bound 1) .newest else .mem (.bound 1) .newest))))
      freeClosed := by cases b <;> simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
      delta0 := .existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..)
        (by cases b; exact .mem _ _; exact .atom _ _ _)))) }
    let ρ := (((⟨fun _ => C, fun _ => C⟩ : Env M 1).push E).push f).push g
    let η := (((⟨fun _ => C', fun _ => C'⟩ : Env M 1).push E').push f').push g'
    have read (ρ : Env M 4) v : φ.toUnarySchema.denote ρ v ↔ ∃ x, M.mem x (ρ.bound 3) ∧ ∃ t, M.mem t (ρ.bound 2) ∧
        Rd_entry_d v x (ρ.bound 1) ∧ Rd_entry_d v t (ρ.bound 0) ∧ (if b then x = t else M.mem x t) := by
      cases b <;> simp only [φ, Bool.false_eq_true, ↓reduceIte, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
        rd_entry0_sat_l hZF.1, Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1] <;> rfl
    have source v : φ.toUnarySchema.denote ρ v ↔ Rp_atom_d I b X R f g v := by
      rw [read]
      constructor
      · rintro ⟨x, hx, t, ht, hfx, hgt, ht'⟩
        refine ⟨x, hX C hCX x hx, t, hX E hEX t ht, hfx, hgt, ?_⟩
        cases b
        · exact (hm.2 x t).mpr ⟨hX C hCX x hx, hX E hEX t ht, ht'⟩
        · exact ht'
      · rintro ⟨x, _, t, _, hfx, hgt, ht'⟩
        refine ⟨x, (hFC.bound_l hfx).2, t, (hGE.bound_l hgt).2, hfx, hgt, ?_⟩
        cases b
        · exact ((hm.2 x t).mp ht').2.2
        · exact ht'
    obtain ⟨V, hVX, vs, vu⟩ := ed_separate_delta_l I hZF hω h hX hY hP hPX hD ha hU φ ρ η
      (Fin.cases hjg (Fin.cases hjf (Fin.cases hjE (fun _ => hjC))))
    have target : φ.toUnarySchema.denote η a ↔ (if b then y = z else M.mem y z) := (read η a).trans
      ⟨fun ⟨x, _, t, _, hfx, hgt, ht⟩ =>
        (fn0_function_l (ZF.modelsKP hZF) ff).1.2 a x y hfx haf ▸
          (fn0_function_l (ZF.modelsKP hZF) gg).1.2 a t z hgt hag ▸ ht,
        fun ht => ⟨y, (ff.bound_l haf).2, z, (gg.bound_l hag).2, haf, hag, ht⟩⟩
    refine ⟨fun ⟨W, hw, truth⟩ => target.mp (vu.mp ?_), fun ht =>
      ⟨V, vu.mpr (target.mpr ht), fun v hv => (source v).mp ((vs v).mp hv).2⟩⟩
    obtain ⟨hWD, W', hjW, haW⟩ := (hU W).mp hw
    obtain ⟨V', _, hjV⟩ := hj.2.2 V hVX
    exact (hU V).mpr ⟨fun v hv => ((vs v).mp hv).1, V', hjV,
      (ed_subset_l I hZF hω h hX hY hjW hjV).mp
        (fun v hv => (vs v).mpr ⟨hWD v hv, (source v).mpr (truth v hv)⟩) a haW⟩
  exact ⟨(rp_atom_eq_l I (R := R)).symm.trans (atom true), atom false⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 派生求值保持带谓词的关系原子

真值集用背景分离得到，并由完整幂集包含于源证明可输入原嵌入。
图求值使用解码后的成员语言；最后的关系原子直接保留谓词结构的关系。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ed_predicate_trace_l {ω c X A R d Y B S j f g H f' g' H' : M.Domain}
    (hω : M.IsOmega ω) (hx : Spred_d I c X A R) (hy : Spred_d I d Y B S)
    (hj : Smap_d I ω c d X Y j) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hf : Rd_entry_d f f' j) (hg : Rd_entry_d g g' j) (hH : Rd_entry_d H H' j)
    (trace : ∀ u v w, M.mem u X → M.mem v X → M.mem w X → Rd_entry_d u v f → Rd_entry_d u w g →
      (M.mem u H ↔ Rd_entry_d v w R)) :
    ∀ u v w, M.mem u Y → M.mem v Y → M.mem w Y → Rd_entry_d u v f' → Rd_entry_d u w g' →
      (M.mem u H' ↔ Rd_entry_d v w S) := by
  let decode {n} (φ : Formula 1 n) := spred_core_l (source_core_l φ)
  have read {Z P T e} (he : Spred_d I e Z P T) (ht : M.TransitiveSet Z) {n}
      (φ : Formula 1 n) (hd : φ.IsDelta0) (ρ : Env (smdl_structure_l I (R := T) he.1.2.1) n) :
      Formula.satisfies ρ (decode φ) ↔ Formula.satisfies ⟨fun i => (ρ.bound i).val, fun i => (ρ.free i).val⟩ φ := by
    obtain ⟨z, hz⟩ := he.1.2.1
    let hn : Nonempty {x // M.mem x Z} := ⟨⟨z, hz⟩⟩
    let ρ' : Env (rt_model_l Z hn) n := ⟨ρ.bound, ρ.free⟩
    exact (spred_core_sat_l I (ZF.modelsKP hZF) he hn (source_core_l φ) ρ').trans
      ((source_core_sat_l φ ρ').trans (rt_model_delta_l ht hn hd ρ'))
  let φ : Formula 1 3 := .forallE (.forallE (.forallE (.imp
    (decode (.conj (rd_entry0_m (.bound 2) (.bound 1) (.bound 3)) (rd_entry0_m (.bound 2) .newest (.bound 4))))
    (.iff (decode (.mem (.bound 2) (.bound 5))) (.mem (.bound 1) .newest)))))
  let ρ : Env (smdl_structure_l I (R := R) hx.1.2.1) 3 := {
    bound := Fin.cases ⟨f, hj.1.1.input_mem_of_pairMember hf⟩
      (Fin.cases ⟨g, hj.1.1.input_mem_of_pairMember hg⟩ (fun _ => ⟨H, hj.1.1.input_mem_of_pairMember hH⟩))
    free := fun _ => ⟨f, hj.1.1.input_mem_of_pairMember hf⟩ }
  let η : Env (smdl_structure_l I (R := S) hy.1.2.1) 3 := {
    bound := Fin.cases ⟨f', hj.1.1.output_mem_of_pairMember hf⟩
      (Fin.cases ⟨g', hj.1.1.output_mem_of_pairMember hg⟩ (fun _ => ⟨H', hj.1.1.output_mem_of_pairMember hH⟩))
    free := fun _ => ⟨f', hj.1.1.output_mem_of_pairMember hf⟩ }
  have tr := smap_source_l I hZF hω hx.1 hy.1 hj φ (by
    simp only [φ, Definitional.Formula.FreeClosed]
    exact ⟨spred_core_closed_l _ (source_core_closed_l _ (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed])),
      spred_core_closed_l _ (source_core_closed_l _ (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed])), by simp⟩)
    ρ η (Fin.cases hf (Fin.cases hg (fun _ => hH)))
  have source : Formula.satisfies ρ φ := by
    simp only [φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff,
      read hx hX _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)), read hx hX _ (.mem _ _),
      Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_mem_iff]
    exact fun u v w huv => trace u.val v.val w.val u.property v.property w.property huv.1 huv.2
  have target := tr.mp source
  simp only [φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff,
    read hy hY _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)), read hy hY _ (.mem _ _),
    Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_mem_iff] at target
  exact fun u v w hu hv hw huv huw => target ⟨u, hu⟩ ⟨v, hv⟩ ⟨w, hw⟩ ⟨huv, huw⟩

theorem ed_predicate_evaluation_l {ω c X A R d Y B S j D D' a U P f g y z : M.Domain}
    (hω : M.IsOmega ω) (hx : Spred_d I c X A R) (hy : Spred_d I d Y B S)
    (hj : Smap_d I ω c d X Y j) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hD : Rd_entry_d D D' j) (ha : M.mem a D') (hP : M.IsPowerSetOf P D) (hPX : M.MemberSubset P X)
    (hU : Ed_filter_d I j a D U) (hf : Sfun_d X D f) (hg : Sfun_d X D g)
    (ey : Ee_value_d j a f y) (ez : Ee_value_d j a g z) : Rp_rel_d I X U R f g ↔ Rd_entry_d y z S := by
  have h : Spred_emb_d I ω X A Y B j := ⟨c, R, d, S, hx, hy, hj⟩
  obtain ⟨_, C, hC, hf⟩ := hf
  obtain ⟨_, E, hE, hg⟩ := hg
  obtain ⟨f', hjf, hay⟩ := ey
  obtain ⟨g', hjg, haz⟩ := ez
  obtain ⟨C', hC', hjC⟩ := hj.1.1.2.2 C hC
  obtain ⟨E', hE', hjE⟩ := hj.1.1.2.2 E hE
  have ff := (spred_function_l I hZF hω h hX hY hD hjC hjf).mp hf
  have gg := (spred_function_l I hZF hω h hX hY hD hjE hjg).mp hg
  let ρ := (((⟨fun _ => X, fun _ => X⟩ : Env M 1).push R).push f).push g
  let φ : UnarySchema 4 := { body := rp_atom_m (𝒞 := kpair_convention_l) false (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨H, hs⟩ := ZF.separation_exists_d hZF φ ρ D
  have spec v : M.mem v H ↔ M.mem v D ∧ Rp_atom_d I false X R f g v :=
    (hs v).trans (and_congr_right fun _ => rp_atom_sat_l I hZF.1 false ..)
  have hHX := hPX H ((hP H).mpr fun v hv => ((spec v).mp hv).1)
  obtain ⟨H', _, hjH⟩ := hj.1.1.2.2 H hHX
  have tr := ed_predicate_trace_l hZF hω hx hy hj hX hY hjf hjg hjH (fun u v w _ hv hw huv huw =>
    (spec u).trans ⟨fun ⟨_, x, _, t, _, hux, hut, hxt⟩ =>
      (fn0_function_l (ZF.modelsKP hZF) hf).1.2 u x v hux huv ▸
        (fn0_function_l (ZF.modelsKP hZF) hg).1.2 u t w hut huw ▸ hxt,
      fun hvw => ⟨(hf.bound_l huv).1, v, hv, w, hw, huv, huw, hvw⟩⟩)
  have value := tr a y z (hY D' (hj.1.1.output_mem_of_pairMember hD) a ha)
    (hY C' hC' y (ff.bound_l hay).2) (hY E' hE' z (gg.bound_l haz).2) hay haz
  have measure := (ed_filter_member_l I hj.1.1.1 hU (fun v hv => ((spec v).mp hv).1) hjH).trans value
  refine ⟨fun ⟨W, hw, truth⟩ => measure.mp ?_, fun ht =>
    ⟨H, measure.mpr ht, fun v hv => ((spec v).mp hv).2⟩⟩
  obtain ⟨hWD, W', hjW, haW⟩ := (hU W).mp hw
  exact (hU H).mpr ⟨fun v hv => ((spec v).mp hv).1, H', hjH,
    (ed_subset_l I hZF hω h hX hY hjW hjH).mp
      (fun v hv => (spec v).mpr ⟨hWD v hv, truth v hv⟩) a haW⟩

end YesMetaZFC.SetTheory.LargeCardinal
