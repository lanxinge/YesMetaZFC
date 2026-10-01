import YesMetaZFC.SetTheory.InnerModel.Order.Certificate
import YesMetaZFC.SetTheory.InnerModel.Rudimentary.SetImage

/-! # Jensen 规范微后继的实际 Σ₁ 图

参数依次为输入序 R、输出序 S；输入、输出槽分别保存载体 U、V。
见证只保存有限构造的中间集合，Δ₀ 矩阵不检查或假定良序性。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def rw_successor_s : S1_binary 2 where
  matrix := {
    -- 量词后的槽位：E,Y,P,Q,A,B,V,U,R,S。
    body := Formula.existsMem .newest <| Formula.existsMem (.bound 1) <| Formula.existsMem (.bound 2) <|
      Formula.existsMem (.bound 3) <| Formula.existsMem (.bound 4) <|
        .conj (pair0_m (.bound 1) (.bound 7) (.bound 7)) <|
          .conj (Formula.forallMem .newest .falsum) <|
            .conj (rw_union_m (.bound 4) (.bound 7) (.bound 1)) <|
              .conj (rw_table_m rw_append_s (.bound 7) (.bound 8) .newest (.bound 4) (.bound 3)) <|
                .conj (rw_domain_m (.bound 4) (.bound 2)) <|
                  rw_fold_cert_m rd_menu_l (.bound 5) (.bound 4) (.bound 3) (.bound 2)
                    (.bound 4) (.bound 3) (.bound 6) (.bound 9)
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
      (.conj (pair0_delta_l ..) (.conj (.forallMem _ .falsum) (.conj (rw_union_delta_l ..)
        (.conj (rw_table_delta_l ..) (.conj (rw_domain_delta_l ..) (rw_fold_cert_delta_l ..)))))))))) }

theorem rw_successor_sat_l (hKP : M.Models KP) (ρ : Env M 2) (U V : M.Domain) :
    rw_successor_s.schema.denote ρ U V ↔ Rw_successor_d U (ρ.bound 0) V (ρ.bound 1) := by
  let η B A Q P Y E := ((((((((ρ.push U).push V).push B).push A).push Q).push P).push Y).push E)
  have fold B A Q P Y E (hp : Rw_domain_d A P) :
      Formula.satisfies (η B A Q P Y E) (rw_fold_cert_m rd_menu_l (.bound 5) (.bound 4) (.bound 3) (.bound 2)
        (.bound 4) (.bound 3) (.bound 6) (.bound 9)) ↔ Rw_fold_cert_d rd_menu_l B A Q P A Q V (ρ.bound 1) :=
    rw_fold_cert_sat_l hKP _ _ _ _ _ _ _ _ _ _ hp
  rw [S1_binary.sat_l]
  simp only [rw_successor_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, pair0_sat_l hKP.1,
    Formula.satisfies_forallMem_iff, Formula.satisfies_falsum_iff, rw_union_sat_l, rw_table_formula_l hKP, rw_domain_sat_l hKP]
  simp only [Rw_rel_d, rw_append_sat_l hKP.1]
  change (∃ B A, M.mem A B ∧ ∃ Q, M.mem Q B ∧ ∃ P, M.mem P B ∧ ∃ Y, M.mem Y B ∧ ∃ E, M.mem E B ∧
    Pair_d M Y U U ∧ (∀ x, M.mem x E → False) ∧ M.IsUnionOfTwo A U Y ∧ Rw_rel_d (Rw_append_d U (ρ.bound 0) E) A Q ∧
    Rw_domain_d A P ∧ Formula.satisfies (η B A Q P Y E) (rw_fold_cert_m rd_menu_l (.bound 5) (.bound 4) (.bound 3) (.bound 2)
      (.bound 4) (.bound 3) (.bound 6) (.bound 9))) ↔ _
  constructor
  · rintro ⟨B, A, _, Q, _, P, _, Y, _, E, _, hy, he, ha, hq, hp, hf⟩
    exact ⟨A, Q, ⟨Y, E, hy, he, ha, hq⟩, ⟨P, hp, rw_fold_cert_sound_l ((fold B A Q P Y E hp).mp hf)⟩⟩
  · rintro ⟨A, Q, ⟨Y, E, hy, he, ha, hq⟩, ⟨P, hp, hf⟩⟩
    obtain ⟨D, hd⟩ := rw_fold_cert_exists_l hKP hf
    obtain ⟨B, hb⟩ := kp_finite_cover_l hKP [A, Q, P, Y, E, D]
    exact ⟨B, A, (hb A (by simp)).2, Q, (hb Q (by simp)).2, P, (hb P (by simp)).2,
      Y, (hb Y (by simp)).2, E, (hb E (by simp)).2, hy, he, ha, hq, hp,
      (fold B A Q P Y E hp).mpr (rw_fold_cert_mono_l hd (hb D (by simp)).1)⟩

/-- 同一个 Σ₁ 公式在任意 KP 背景上定义唯一的有序微后继。 -/
theorem rw_successor_defined_l (hKP : M.Models KP) (U R : M.Domain) : ∃ V S,
    rw_successor_s.schema.denote (⟨Fin.cases R (fun _ => S), fun _ => U⟩ : Env M 2) U V ∧
      ∀ V' S', rw_successor_s.schema.denote (⟨Fin.cases R (fun _ => S'), fun _ => U⟩ : Env M 2) U V' → V' = V ∧ S' = S := by
  obtain ⟨V, S, h⟩ := rw_successor_exists_l hKP U R
  exact ⟨V, S, (rw_successor_sat_l hKP _ U V).mpr h, fun V' S' h' =>
    rw_successor_unique_l hKP.1 ((rw_successor_sat_l hKP _ U V').mp h') h⟩

/-- 载体的局部性：微后继集合本身仍属于原有限基闭包。 -/
theorem rw_successor_carrier_closed_l (hKP : M.Models KP) {C U R V S : M.Domain}
    (hC : Rd_closed_d C) (hU : M.mem U C) (hu : M.TransitiveSet U) (h : Rw_successor_d U R V S) : M.mem V C := by
  obtain ⟨A, Q, ha, hv⟩ := h
  have hs := rw_adjoin_carrier_l hKP.1 ha
  obtain ⟨Y, hYC, hy⟩ := hC.exists_l hKP .pair hU hU hU
  obtain ⟨A', hAC, hA⟩ := hC.union_l hKP hU hYC
  have heq : A' = A := hKP.1.eq_of_same_members _ _ fun x => (hA x).trans
    ((or_congr Iff.rfl ((hy x).trans ⟨fun h => (h.elim id id) ▸ (fun _ => Iff.rfl),
      fun h => Or.inl (hKP.1.eq_of_same_members x U h)⟩)).trans (hs x).symm)
  have hAC : M.mem A C := heq ▸ hAC
  apply rd_step_closed_l hKP hC hAC _ (rw_step_carrier_l hKP hv)
  intro x hx y hy
  exact (hs y).mpr (Or.inl (((hs x).mp hx).elim (fun hx => hu x hx y hy)
    (fun he => hKP.1.eq_of_same_members x U he ▸ hy)))

end YesMetaZFC.SetTheory.InnerModel
