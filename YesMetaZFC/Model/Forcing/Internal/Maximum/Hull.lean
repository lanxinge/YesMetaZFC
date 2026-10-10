import YesMetaZFC.Model.Forcing.Internal.Names.Closure

/-! # 输入名称的唯一最小闭名称库

对所有包含给定两名称的闭支撑取交：先用任一共同闭支撑给出集合界，再按
实际原公式分离。所得最小库与最初见证无关，可用于确定的后继递归装配。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

structure Name_hull_d (B s t W : M.Domain) : Prop where
  left : M.mem s W
  right : M.mem t W
  closed : Supp_d M B W
  least : ∀ S, M.mem s S → M.mem t S → Supp_d M B S → M.MemberSubset W S

def name_hull_m {n} (B s t W : Term n) : Formula 1 n :=
  .conj (.mem s W) (.conj (.mem t W) (.conj (supp_m B W)
    (.forallE (.imp (.mem s.weaken .newest) (.imp (.mem t.weaken .newest)
      (.imp (supp_m B.weaken .newest) (Formula.subset W.weaken .newest)))))))
derive_free_closed name_hull_m

theorem name_hull_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B s t W : Term n) :
    Formula.satisfies ρ (name_hull_m B s t W) ↔
      Name_hull_d M (B.eval ρ) (s.eval ρ) (t.eval ρ) (W.eval ρ) := by
  simp only [name_hull_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    supp_sat_l M hE, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_subset_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨h.left, h.right, h.closed, h.least⟩⟩

/-- 最小闭库在原 ZF 内存在；没有选定泛型，也不沿外部良基关系递归。 -/
theorem name_hull_exists_l (hZF : M.Models ZF) {B s t} (hs : Name_d M B s) (ht : Name_d M B t) :
    ∃ W, Name_hull_d M B s t W := by
  obtain ⟨S, hsS, htS, hS⟩ := name_support_l M (KP.exists_pair (ZF.modelsKP hZF))
    (KP.exists_union (ZF.modelsKP hZF)) hs ht
  let ρ : Env M 3 := ((⟨fun _ => B, fun _ => B⟩ : Env M 1).push s).push t
  let φ : UnarySchema 3 := {
    body := .forallE (.imp (.mem (.bound 3) .newest) (.imp (.mem (.bound 2) .newest)
      (.imp (supp_m (.bound 4) .newest) (.mem (.bound 1) .newest)))) }
  have hφ x : φ.denote ρ x ↔ ∀ U, M.mem s U → M.mem t U → Supp_d M B U → M.mem x U := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_mem_iff, supp_sat_l M hZF.1]
    rfl
  obtain ⟨W, hW'⟩ := ZF.separation_exists_d hZF φ ρ S
  have hW x : M.mem x W ↔ ∀ U, M.mem s U → M.mem t U → Supp_d M B U → M.mem x U := by
    refine (hW' x).trans ?_
    change (M.mem x S ∧ φ.denote ρ x) ↔ _
    rw [hφ x]
    exact ⟨And.right, fun hx => ⟨hx S hsS htS hS, hx⟩⟩
  refine ⟨W, ⟨(hW s).mpr (fun _ hs _ _ => hs), (hW t).mpr (fun _ _ ht _ => ht), ?_, ?_⟩⟩
  · intro x hx v hv
    obtain ⟨a, b, hab, _, hb⟩ := hS x ((hW x).mp hx S hsS htS hS) v hv
    exact ⟨a, b, hab, (hW a).mpr (fun U hsU htU hU =>
      (supp_entry_l M hU ((hW x).mp hx U hsU htU hU) ⟨v, hab, hv⟩).1), hb⟩
  · exact fun U hsU htU hU x hx => (hW x).mp hx U hsU htU hU

theorem name_hull_unique_l (hE : Extensional M) {B s t W W'}
    (h : Name_hull_d M B s t W) (h' : Name_hull_d M B s t W') : W = W' :=
  hE.eq_of_same_members W W' (fun x =>
    ⟨h.least W' h'.left h'.right h'.closed x, h'.least W h.left h.right h.closed x⟩)

end YesMetaZFC.Model.Forcing.Internal
