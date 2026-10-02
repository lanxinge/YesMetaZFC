import YesMetaZFC.SetTheory.Descriptive.Projective.Hierarchy

/-! # 全部内部射影层的实际集合图

每层 Σ、Π 类都是 P(B) 的内部子集，Δ 类为它们的交；再把层号送到有序对
(Σ,Π)，形成定义域恰为内部 ω 的实际函数图。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Plevel_d (ω A B J n p : M.Domain) : Prop := ∃ S P, I.Codes p S P ∧
  (∀ K, M.mem K S ↔ Ps_d I ω A B J n K) ∧ ∀ K, M.mem K P ↔ Pp_d I ω A B J n K
def plevel_m {d} (ω A B J n p : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (𝒞.code p.weaken.weaken (.bound 1) .newest) (.conj
  (.forallE (.iff (.mem .newest (.bound 2)) (ps_m (𝒞 := 𝒞) ω.weaken.weaken.weaken
    A.weaken.weaken.weaken B.weaken.weaken.weaken J.weaken.weaken.weaken n.weaken.weaken.weaken .newest)))
  (.forallE (.iff (.mem .newest (.bound 1)) (pp_m (𝒞 := 𝒞) ω.weaken.weaken.weaken
    A.weaken.weaken.weaken B.weaken.weaken.weaken J.weaken.weaken.weaken n.weaken.weaken.weaken .newest))))))
derive_free_closed plevel_m
@[prove_auto_norm semantic]
theorem plevel_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J n p : Term d) :
    Formula.satisfies ρ (plevel_m (𝒞 := 𝒞) ω A B J n p) ↔
      Plevel_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (n.eval ρ) (p.eval ρ) := by
  simp only [plevel_m, Plevel_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    I.satisfies_code_iff, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, ps_sat_l I hE, pp_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem plevel_unique_l (hE : Extensional M) {ω A B J n p q}
    (h : Plevel_d I ω A B J n p) (k : Plevel_d I ω A B J n q) : p = q := by
  obtain ⟨S, P, hp, hs, ht⟩ := h
  obtain ⟨S', P', hq, hs', ht'⟩ := k
  have e := hE.eq_of_same_members S S' (fun K => (hs K).trans (hs' K).symm)
  subst S'
  have e := hE.eq_of_same_members P P' (fun K => (ht K).trans (ht' K).symm)
  subst P'
  exact I.unique hp hq

theorem plevel_exists_l (hZF : M.Models ZF) (ω A B J n : M.Domain) : ∃ p, Plevel_d I ω A B J n p := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF B
  let ρ : Env M 5 := ((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J).push n
  let φ : UnarySchema 5 := { body := ps_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  let ψ : UnarySchema 5 := { body := pp_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨S, hS'⟩ := ZF.separation_exists_d hZF φ ρ P
  obtain ⟨Q, hQ'⟩ := ZF.separation_exists_d hZF ψ ρ P
  have hS K : M.mem K S ↔ Ps_d I ω A B J n K := ((hS' K).trans
    (and_congr_right fun _ => ps_sat_l I hZF.1 _ _ _ _ _ _ _)).trans
      ⟨And.right, fun h => ⟨(hP K).mpr (ps_subset_l I h), h⟩⟩
  have hQ K : M.mem K Q ↔ Pp_d I ω A B J n K := ((hQ' K).trans
    (and_congr_right fun _ => pp_sat_l I hZF.1 _ _ _ _ _ _ _)).trans
      ⟨And.right, fun h => ⟨(hP K).mpr (h.elim fun _ h => fun x hx => ((h.2 x).mp hx).1), h⟩⟩
  obtain ⟨p, hp⟩ := I.total S Q
  exact ⟨p, S, Q, hp, hS, hQ⟩

theorem plevel_delta_l (hKP : M.Models KP) {ω A B J n p} (h : Plevel_d I ω A B J n p) :
    ∃ D, ∀ K, M.mem K D ↔ Pd_d I ω A B J n K := by
  obtain ⟨S, P, _, hs, hp⟩ := h
  obtain ⟨D, hD⟩ := KP.intersection_exists_d hKP S P
  exact ⟨D, fun K => (hD K).trans (and_congr (hs K) (hp K))⟩

def Phier_d (ω A B J H : M.Domain) : Prop := M.IsSetFunction I H ∧ ∀ n p,
  M.PairMember I n p H ↔ M.mem n ω ∧ Plevel_d I ω A B J n p
def phier_m {d} (ω A B J H : Term d) : Formula 1 d := .conj (Formula.isFunction 𝒞 H)
  (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest H.weaken.weaken)
    (.conj (.mem (.bound 1) ω.weaken.weaken) (plevel_m (𝒞 := 𝒞) ω.weaken.weaken
      A.weaken.weaken B.weaken.weaken J.weaken.weaken (.bound 1) .newest)))))
derive_free_closed phier_m
@[prove_auto_norm semantic]
theorem phier_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J H : Term d) :
    Formula.satisfies ρ (phier_m (𝒞 := 𝒞) ω A B J H) ↔
      Phier_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (H.eval ρ) := by
  simp only [phier_m, Phier_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, plevel_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem phier_exists_unique_l (hZF : M.Models ZF) (ω A B J : M.Domain) :
    ∃ H, Phier_d I ω A B J H ∧ ∀ G, Phier_d I ω A B J G → G = H := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF B
  obtain ⟨Q, hQ⟩ := ZF.exists_powerSet hZF P
  obtain ⟨V, hV⟩ := ZF.exists_cartesianProduct hZF I Q Q
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J
  let φ : BinarySchema 4 := { body := plevel_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hp n p : φ.denote ρ n p ↔ Plevel_d I ω A B J n p := plevel_sat_l I hZF.1 _ _ _ _ _ _ _
  obtain ⟨H, hH, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := V)
    (fun n _ => (plevel_exists_l I hZF ω A B J n).imp fun p h => (hp n p).mpr h)
    (fun n _ p q h k => plevel_unique_l I hZF.1 ((hp n p).mp h) ((hp n q).mp k))
    (by
      intro n p _ h
      obtain ⟨S, R, hp, hs, hr⟩ := (hp n p).mp h
      exact (hV p).mpr ⟨S, (hQ S).mpr (fun K hK => (hP K).mpr (ps_subset_l I ((hs K).mp hK))),
        R, (hQ R).mpr (fun K hK => (hP K).mpr (((hr K).mp hK).elim fun L h => fun x hx => ((h.2 x).mp hx).1)), hp⟩)
  have hh : Phier_d I ω A B J H := ⟨hH.1, fun n p => (he n p).trans (and_congr_right fun _ => hp n p)⟩
  exact ⟨H, hh, fun G hg => hg.1.1.eq_of_pairMember_iff hZF.1 hh.1.1
    (fun n p => (hg.2 n p).trans (hh.2 n p).symm)⟩

end YesMetaZFC.SetTheory.Descriptive
