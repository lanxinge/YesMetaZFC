import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.RelationSyntax

/-! # 原关系代表族的一阶规格

规格保留内部函数码及其实际坐标图，供全部支撑的一次替换使用。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Rc_family_d (Y S D d t G : M.Domain) : Prop := ∀ g, M.mem g G ↔ Fn0_d D Y g ∧
  ∃ f, Rf_fun_d I Y S d f ∧ Rc_graph_d I Y S t f g

def rc_family_m {n} (Y S D d t G : Term n) : Formula 1 n := .forallE
  (.iff (.mem .newest G.weaken) (.conj (fn0_m D.weaken Y.weaken .newest) (.existsE
    (.conj (rf_fun_m (𝒞 := kpair_convention_l) Y.weaken.weaken S.weaken.weaken d.weaken.weaken .newest)
      (rc_graph_m (𝒞 := kpair_convention_l) Y.weaken.weaken S.weaken.weaken t.weaken.weaken .newest (.bound 1))))))
derive_free_closed rc_family_m

theorem rc_family_sat_l (hE : Extensional M) {n} (ρ : Env M n) (Y S D d t G : Term n) :
    Formula.satisfies ρ (rc_family_m Y S D d t G) ↔
      Rc_family_d I (Y.eval ρ) (S.eval ρ) (D.eval ρ) (d.eval ρ) (t.eval ρ) (G.eval ρ) := by
  simp only [rc_family_m, Rc_family_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, fn0_sat_l hE,
    Formula.satisfies_exists_iff, rf_fun_sat_l I, rc_graph_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem rc_family_native_l {Y S D t G : M.Domain} (ny : ∃ y, M.mem y Y)
    (en : Extensional (smdl_structure_l I (R := S) ny))
    (d : (smdl_structure_l I (R := S) ny).Domain) (ft : Fn0_d D Y t) :
    Rc_family_d I Y S D d.val t G ↔ ∀ g, M.mem g G ↔ Fn0_d D Y g ∧
      ∃ B f : (smdl_structure_l I (R := S) ny).Domain, Fn0_d d B f ∧
        ∀ s (x y : (smdl_structure_l I (R := S) ny).Domain), Rd_entry_d s x.val t →
          (Rd_entry_d s y.val g ↔ Rd_entry_d x y f) := by
  have read g (fg : Fn0_d D Y g) :
      (∃ f, Rf_fun_d I Y S d.val f ∧ Rc_graph_d I Y S t f g) ↔
        ∃ B f : (smdl_structure_l I (R := S) ny).Domain, Fn0_d d B f ∧
          ∀ s (x y : (smdl_structure_l I (R := S) ny).Domain), Rd_entry_d s x.val t →
            (Rd_entry_d s y.val g ↔ Rd_entry_d x y f) := by
    constructor
    · rintro ⟨f, ff, graph⟩
      obtain ⟨B, fb⟩ := (rf_fun_native_l I ny en d ⟨f, ff.mem_l I⟩).mp ff
      exact ⟨B, ⟨f, ff.mem_l I⟩, fb, (rc_graph_native_l I ny en ft fg _).mp graph⟩
    · rintro ⟨B, f, ff, graph⟩
      exact ⟨f.val, (rf_fun_native_l I ny en d f).mpr ⟨B, ff⟩, (rc_graph_native_l I ny en ft fg f).mpr graph⟩
  exact forall_congr' fun g => iff_congr Iff.rfl (and_congr_right (read g))

end YesMetaZFC.SetTheory.Internal
