import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Bounded

/-! # 内部四元组的唯一坐标与传递容器读取 -/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem Rd_triple_d.unique_l {s x y z x' y' z' : M.Domain}
    (h : Rd_triple_d s x y z) (g : Rd_triple_d s x' y' z') : x = x' ∧ y = y' ∧ z = z' := by
  obtain ⟨p, hp, hs⟩ := h
  obtain ⟨q, hq, gs⟩ := g
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hs gs
  exact ⟨rfl, kpair_injective_l M hp hq⟩

def Rd_quad_d (s x y z w : M.Domain) : Prop := ∃ p, KPair_d M p z w ∧ Rd_triple_d s x y p
def rd_quad_m {d} (s x y z w : Term d) : Formula 1 d := .existsE
  (.conj (kpair0_m .newest z.weaken w.weaken) (rd_triple0_m s.weaken x.weaken y.weaken .newest))
derive_free_closed rd_quad_m
theorem rd_quad_sat_l (hE : Extensional M) {d} (η : Env M d) (s x y z w : Term d) :
    Formula.satisfies η (rd_quad_m s x y z w) ↔ Rd_quad_d (s.eval η) (x.eval η) (y.eval η) (z.eval η) (w.eval η) := by
  simp only [rd_quad_m, Rd_quad_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hE, rd_triple0_sat_l hE, Definitional.Term.eval_weaken]; rfl
theorem rd_quad_exists_l (hKP : M.Models KP) (x y z w : M.Domain) : ∃ s, Rd_quad_d s x y z w := by
  let I := kpair_interpretation_l M hKP.1 (KP.exists_pair hKP)
  obtain ⟨p, hp⟩ := I.total z w
  obtain ⟨q, hq⟩ := I.total y p
  obtain ⟨s, hs⟩ := I.total x q
  exact ⟨s, p, hp, q, hq, hs⟩
theorem Rd_quad_d.unique_l {s x y z w x' y' z' w' : M.Domain}
    (h : Rd_quad_d s x y z w) (g : Rd_quad_d s x' y' z' w') : x = x' ∧ y = y' ∧ z = z' ∧ w = w' := by
  obtain ⟨p, hp, q, hq, hs⟩ := h
  obtain ⟨p', hp', q', hq', hs'⟩ := g
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hs hs'
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hq hq'
  exact ⟨rfl, rfl, kpair_injective_l M hp hp'⟩
theorem Rd_quad_d.mem_l {Z s x y z w : M.Domain} (hZ : M.TransitiveSet Z) (hs : M.mem s Z)
    (h : Rd_quad_d s x y z w) : M.mem x Z ∧ M.mem y Z ∧ M.mem z Z ∧ M.mem w Z := by
  obtain ⟨p, hp, q, hq, code⟩ := h
  have h₀ := code.mem_l M hZ hs
  have h₁ := hq.mem_l M hZ h₀.2
  exact ⟨h₀.1, h₁.1, hp.mem_l M hZ h₁.2⟩

end YesMetaZFC.SetTheory.InnerModel
