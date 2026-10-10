import YesMetaZFC.SetTheory.InnerModel.OD.Complexity
import YesMetaZFC.SetTheory.TransitiveClosure

/-! # HOD 的内部成员谓词

用一个全部成员属于 OD 的传递容器见证遗传可定义性，并证明其与 TC({x})
的通常定义等价。见证、序数和传递性均按原模型解释。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Hod_d (x : M.Domain) : Prop := ∃ T, M.TransitiveSet T ∧ M.mem x T ∧ ∀ y, M.mem y T → Od_d y

def hod_m {d} (x : Term d) : Formula 1 d := .existsE (.conj (Formula.isTransitive .newest)
  (.conj (.mem x.weaken .newest) (Formula.forallMem .newest (od_m .newest))))
derive_free_closed hod_m

theorem hod_sat_l {d} (ρ : Env M d) (x : Term d) : Formula.satisfies ρ (hod_m x) ↔ Hod_d (x.eval ρ) := by
  simp only [hod_m, Hod_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isTransitive_iff, Formula.satisfies_mem_iff, Formula.satisfies_forallMem_iff,
    od_sat_l, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem hod_od_l {x : M.Domain} (h : Hod_d x) : Od_d x := h.elim fun _ h => h.2.2 x h.2.1

theorem hod_transitive_l {x y : M.Domain} (h : Hod_d x) (hy : M.mem y x) : Hod_d y := by
  obtain ⟨T, ht, hx, ho⟩ := h
  exact ⟨T, ht, ht x hx y hy, ho⟩

theorem hod_tc_l (hZF : M.Models ZF) {x : M.Domain} : Hod_d x ↔
    ∃ T, Tc_d x T ∧ ∀ y, M.mem y T → Od_d y := by
  constructor
  · rintro ⟨S, hs, hx, ho⟩
    obtain ⟨T, ht⟩ := ZF.tc_exists_l (kp_pair_l (ZF.modelsKP hZF)) hZF x
    exact ⟨T, ht, fun y hy => ho y (ht.2.2 S hs hx y hy)⟩
  · exact fun ⟨T, ht, ho⟩ => ⟨T, ht.1, ht.2.1, ho⟩

/-- 一个 OD 集合若包含于遗传 OD 容器，则本身属于 HOD。 -/
theorem hod_bounded_l (hKP : M.Models KP) {T x : M.Domain} (ht : M.TransitiveSet T)
    (ho : ∀ y, M.mem y T → Od_d y) (hx : Od_d x) (hs : M.MemberSubset x T) : Hod_d x := by
  obtain ⟨S, hS⟩ := KP.exists_insert hKP T x
  refine ⟨S, ?_, (hS x).mpr (Or.inr rfl), fun y hy => ((hS y).mp hy).elim (ho y) (fun he => he.symm ▸ hx)⟩
  intro y hy z hz
  exact (hS z).mpr (Or.inl (((hS y).mp hy).elim (fun hy => ht y hy z hz) (fun he => hs z (he ▸ hz))))

theorem hod_ordinal_l (hZF : M.Models ZF) {x : M.Domain} (hx : M.IsOrdinal x) : Hod_d x := by
  obtain ⟨s, hs, hxs⟩ := KP.ordinal_successor_l (ZF.modelsKP hZF) hx
  exact ⟨s, hs.transitive, hxs.predecessor_mem, fun y hy => od_ordinal_l hZF (hs.mem hy)⟩

def hod_sigma_m {d} (x : Term d) : Formula 1 d := .existsE (.conj (Formula.isTransitive .newest)
  (.conj (.mem x.weaken .newest) (Formula.forallMem .newest (od_sigma_m .newest))))
derive_free_closed hod_sigma_m

theorem hod_sigma_complexity_l {d} (x : Term d) : (hod_sigma_m x).IsSigma2 :=
  .existsE (.conj (.lift (.lift (.base (Formula.isTransitive_delta0 _))))
    (.conj (.lift (.lift (.base (.mem _ _)))) (.forallMem _ (od_sigma_complexity_l _))))

theorem hod_sigma_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (x : Term d) :
    Formula.satisfies ρ (hod_sigma_m x) ↔ Hod_d (x.eval ρ) := by
  simp only [hod_sigma_m, Hod_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isTransitive_iff, Formula.satisfies_mem_iff, Formula.satisfies_forallMem_iff,
    od_sigma_sat_l hZF, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

end YesMetaZFC.SetTheory.InnerModel
