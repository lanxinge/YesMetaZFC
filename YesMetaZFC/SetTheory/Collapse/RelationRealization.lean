import YesMetaZFC.SetTheory.Collapse.RelationMap

/-! # 同一有界呈示在一般外延关系中的实现

实际传递像与关系像共有同一批代表。两边都完整反映代表关系，关系像还
覆盖每个已到达点的全部前驱，故相同传递值恰好对应相同关系值。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Wc_map_d.realize_l {A R B e C W v : M.Domain} (map : Wc_map_d A R B e)
    (exact : ∀ u w x y, Rd_entry_d u x e → Rd_entry_d w y e → (Rd_entry_d u w R ↔ M.mem x y))
    (fv : Fn0_d A C v) (ext : Wc_ext_d C W)
    (relation : ∀ u w E H, Rd_entry_d u E v → Rd_entry_d w H v → (Rd_entry_d u w R ↔ Rd_entry_d E H W))
    (cover : ∀ u E, Rd_entry_d u E v → ∀ H, Rd_entry_d H E W → ∃ w, M.mem w A ∧ Rd_entry_d w H v) :
    ∃ k, M.IsSetInjectionFromTo I k B C ∧
      (∀ x E, Rd_entry_d x E k ↔ ∃ u, M.mem u A ∧ Rd_entry_d u x e ∧ Rd_entry_d u E v) ∧
      (∀ x y E H, Rd_entry_d x E k → Rd_entry_d y H k → (M.mem x y ↔ Rd_entry_d E H W)) ∧
      ∀ x E, Rd_entry_d x E k → ∀ H, Rd_entry_d H E W ↔ ∃ y, M.mem y x ∧ Rd_entry_d y H k := by
  have kernel u w x y E H (hx : Rd_entry_d u x e) (hy : Rd_entry_d w y e)
      (hE : Rd_entry_d u E v) (hH : Rd_entry_d w H v) : x = y ↔ E = H := by
    constructor
    · intro eq
      subst y
      apply ext E (fv.bound_l hE).2 H (fv.bound_l hH).2
      intro P _
      have forward u w E H (hx : Rd_entry_d u x e) (hy : Rd_entry_d w x e)
          (hE : Rd_entry_d u E v) (hH : Rd_entry_d w H v) (edge : Rd_entry_d P E W) : Rd_entry_d P H W := by
        obtain ⟨t, ht, htP⟩ := cover u E hE P edge
        obtain ⟨z, _, htz⟩ := map.function.2.1 t ht
        exact (relation t w P H htP hH).mp ((exact t w z x htz hy).mpr
          ((exact t u z x htz hx).mp ((relation t u P E htP hE).mpr edge)))
      exact ⟨forward u w E H hx hy hE hH, forward w u H E hy hx hH hE⟩
    · intro eq
      subst H
      apply hZF.1.eq_of_same_members x y
      intro z
      have forward u w x y (hx : Rd_entry_d u x e) (hy : Rd_entry_d w y e)
          (hE : Rd_entry_d u E v) (hH : Rd_entry_d w E v) (hz : M.mem z x) : M.mem z y := by
        obtain ⟨t, ht, htz⟩ := map.onto z (map.transitive x (map.function.bound_l hx).2 z hz)
        obtain ⟨P, _, htP⟩ := fv.2.1 t ht
        exact (exact t w z y htz hy).mp ((relation t w P E htP hH).mpr
          ((relation t u P E htP hE).mp ((exact t u z x htz hx).mpr hz)))
      exact ⟨forward u w x y hx hy hE hH, forward w u y x hy hx hH hE⟩
  let ρ : Env M 3 := ⟨Fin.cases v (Fin.cases e (fun _ => A)), fun _ => A⟩
  let φ : BinarySchema 3 := {
    body := Formula.existsMem (.bound 4)
      (.conj (rd_entry0_m .newest (.bound 2) (.bound 4)) (rd_entry0_m .newest (.bound 1) (.bound 3))) }
  have sat x E : φ.denote ρ x E ↔ ∃ u, M.mem u A ∧ Rd_entry_d u x e ∧ Rd_entry_d u E v := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨k, fk, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := B) (target := C)
    (fun x hx => by
      obtain ⟨u, hu, hux⟩ := map.onto x hx
      obtain ⟨E, _, huE⟩ := fv.2.1 u hu
      exact ⟨E, (sat x E).mpr ⟨u, hu, hux, huE⟩⟩)
    (fun x _ E H he hh => by
      obtain ⟨u, _, hux, huE⟩ := (sat x E).mp he
      obtain ⟨w, _, hwx, hwH⟩ := (sat x H).mp hh
      exact (kernel u w x x E H hux hwx huE hwH).mp rfl)
    (fun x E _ he => ((sat x E).mp he).elim fun _ h => (fv.bound_l h.2.2).2)
  have read x E : Rd_entry_d x E k ↔ ∃ u, M.mem u A ∧ Rd_entry_d u x e ∧ Rd_entry_d u E v :=
    (spec x E).trans ((and_congr_right fun _ => sat x E).trans
      ⟨And.right, fun h => ⟨h.elim fun _ h => (map.function.bound_l h.2.1).2, h⟩⟩)
  have member x y E H (hx : Rd_entry_d x E k) (hy : Rd_entry_d y H k) : M.mem x y ↔ Rd_entry_d E H W := by
    obtain ⟨u, _, hux, huE⟩ := (read x E).mp hx
    obtain ⟨w, _, hwy, hwH⟩ := (read y H).mp hy
    exact (exact u w x y hux hwy).symm.trans (relation u w E H huE hwH)
  refine ⟨k, ⟨fk, fun x y E hx hy => ?_⟩, read, member, fun x E hx H => ⟨?_, ?_⟩⟩
  · obtain ⟨u, _, hux, huE⟩ := (read x E).mp hx
    obtain ⟨w, _, hwy, hwE⟩ := (read y E).mp hy
    exact (kernel u w x y E E hux hwy huE hwE).mpr rfl
  · intro edge
    obtain ⟨u, _, hux, huE⟩ := (read x E).mp hx
    obtain ⟨w, hw, hwH⟩ := cover u E huE H edge
    obtain ⟨y, _, hwy⟩ := map.function.2.1 w hw
    have hy := (read y H).mpr ⟨w, hw, hwy, hwH⟩
    exact ⟨y, (member y x H E hy hx).mpr edge, hy⟩
  · rintro ⟨y, hxy, hy⟩
    exact (member y x H E hy hx).mp hxy

end YesMetaZFC.SetTheory
