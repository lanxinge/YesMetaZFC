import YesMetaZFC.Model.SetTheory.Internal.PredicateSource
import YesMetaZFC.SetTheory.Filter.Relative

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
  exact ⟨U, fun s => (ht s).trans (and_congr (hP s) Iff.rfl), hu.full_l hZF hP⟩

end YesMetaZFC.SetTheory.LargeCardinal
