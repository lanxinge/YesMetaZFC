import YesMetaZFC.SetTheory.InnerModel.Relative.Reals

/-! # 无选择的规范 L(ℝ) 模型

以唯一实数基集的存在量词定义成员类，再直接取子类型隶属结构。
不通过 Classical.choose 选择 ω、实数空间、传递闭包或模型。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

theorem lr_seed_unique_l {ω B S v C T : M.Domain} (h : Lr_seed_d hZF ω B S) (k : Lr_seed_d hZF v C T) :
    ω = v ∧ B = C ∧ S = T := by
  have ev : ω = v := hZF.1.eq_of_same_members ω v (fun n =>
    ⟨h.1.1.2 v k.1.1.1 n, k.1.1.2 ω h.1.1.1 n⟩)
  subst v
  have eB := baire_unique_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1 h.1 k.1
  subst C
  exact ⟨rfl, rfl, tc_unique_l hZF.1 h.2 k.2⟩

def Lr_d (x : M.Domain) : Prop := ∃ ω B S, Lr_seed_d hZF ω B S ∧ La_d S x

theorem lr_iff_l {ω B S : M.Domain} (h : Lr_seed_d hZF ω B S) (x : M.Domain) :
    Lr_d hZF x ↔ La_d S x := by
  refine ⟨?_, fun hx => ⟨ω, B, S, h, hx⟩⟩
  rintro ⟨v, C, T, k, hx⟩
  exact (lr_seed_unique_l hZF k h).2.2 ▸ hx

def lr_m {d} (x : Term d) : Formula 1 d := .existsE (.existsE (.existsE
  (.conj (baire_m (𝒞 := kpair_convention_l) (.bound 2) (.bound 1))
    (.conj (tc_m (.bound 1) .newest) (la_m .newest x.weaken.weaken.weaken)))))
derive_free_closed lr_m

theorem lr_sat_l {d} (ρ : Env M d) (x : Term d) :
    Formula.satisfies ρ (lr_m x) ↔ Lr_d hZF (x.eval ρ) := by
  simp only [lr_m, Lr_d, Lr_seed_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    baire_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1, tc_sat_l, la_sat_l (ZF.modelsKP hZF),
    Definitional.Term.eval_weaken]
  exact exists_congr fun ω => exists_congr fun B => exists_congr fun S => and_assoc.symm

def lr_model_l : Structure.{u} where
  Domain := {x : M.Domain // Lr_d hZF x}
  nonempty := (lr_seed_exists_l hZF).elim fun ω h => h.elim fun B h => h.elim fun S h =>
    ⟨⟨S, ω, B, S, h, la_seed_l S (ZF.models_kpi_l hZF)⟩⟩
  mem x y := M.mem x.val y.val

/-- 唯一起层识别两种构造；等式只使用谓词外延性，不选择任何集合。 -/
theorem lr_model_eq_l {ω B S : M.Domain} (h : Lr_seed_d hZF ω B S) :
    lr_model_l hZF = la_model_l S (ZF.models_kpi_l hZF) := by
  have he : Lr_d hZF = La_d S := funext (fun x => propext (lr_iff_l hZF h x))
  have lift (P Q : M.Domain → Prop) (hp : Nonempty {x // P x}) (hq : Nonempty {x // Q x}) (e : P = Q) :
      ({ Domain := {x // P x}, nonempty := hp, mem := fun x y => M.mem x.val y.val } : Structure) =
      { Domain := {x // Q x}, nonempty := hq, mem := fun x y => M.mem x.val y.val } := by cases e; rfl
  exact lift _ _ _ _ he

theorem lr_model_zf_l : (lr_model_l hZF).Models ZF := by
  obtain ⟨ω, B, S, h⟩ := lr_seed_exists_l hZF
  rw [lr_model_eq_l hZF h]
  exact la_model_zf_l S hZF h.2.1

theorem lr_transitive_l {x y : M.Domain} (hx : Lr_d hZF x) (hy : M.mem y x) : Lr_d hZF y := by
  obtain ⟨ω, B, S, h, hx⟩ := hx
  exact ⟨ω, B, S, h, la_transitive_l S (ZF.models_kpi_l hZF) h.2.1 hx hy⟩

theorem lr_ordinal_l {a : M.Domain} (ha : M.IsOrdinal a) : Lr_d hZF a := by
  obtain ⟨ω, B, S, h⟩ := lr_seed_exists_l hZF
  exact ⟨ω, B, S, h, la_ordinal_l S (ZF.models_kpi_l hZF) h.2.1 ha⟩

/-- 模型的包含映射保持全部原实数，不仅保持已选的外部标准序列。 -/
theorem lr_real_l {ω B x : M.Domain} (hB : Baire_d (kp_pair_l (ZF.modelsKP hZF)) ω B)
    (hx : M.mem x B) : Lr_d hZF x := by
  obtain ⟨S, hS⟩ := ZF.tc_exists_l (kp_pair_l (ZF.modelsKP hZF)) hZF B
  have hM := ZF.models_kpi_l hZF
  exact ⟨ω, B, S, ⟨hB, hS⟩, la_transitive_l S hM hS.1
    (la_transitive_l S hM hS.1 (la_seed_l S hM) hS.2.1) hx⟩

end YesMetaZFC.SetTheory.InnerModel.Relative
