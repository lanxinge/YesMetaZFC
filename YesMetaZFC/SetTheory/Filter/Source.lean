import YesMetaZFC.SetTheory.Filter.Relative
import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Hull
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph

/-! # 实际源集合拥有的子集与函数

从 X 中分离 D 的全部源内部子集。差集与交集的封闭来自已有 rudimentary 闭包，
常值代表也在 X 内直接构造；不假定 X 包含全部背景子集或函数。
-/
namespace YesMetaZFC.SetTheory.FilterZF
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Source_d (X D B : M.Domain) : Prop := ∀ A, M.mem A B ↔ M.mem A X ∧ M.MemberSubset A D

def source_m {n} (X D B : Term n) : Formula 1 n := .forallE (.iff (.mem .newest B.weaken)
  (.conj (.mem .newest X.weaken) (Formula.subset .newest D.weaken)))
derive_free_closed source_m

theorem source_sat_l {n} (ρ : Env M n) (X D B : Term n) : Formula.satisfies ρ (source_m X D B) ↔
    Source_d (X.eval ρ) (D.eval ρ) (B.eval ρ) := by
  simp only [source_m, Source_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]
  rfl

theorem source_field_exists_l (hKP : M.Models KP) {X D} (hc : Rd_closed_d X) (hD : M.mem D X) :
    ∃ B, Source_d X D B ∧ Field_d D B := by
  let φ : Delta0UnarySchema 1 := { body := Formula.subset .newest (.bound 1), delta0 := .atom _ _ _ }
  obtain ⟨B, hb⟩ := KP.separation_exists_d hKP φ ⟨fun _ => D, fun _ => D⟩ X
  have hB : Source_d X D B := fun A => (hb A).trans (and_congr_right fun _ => Formula.satisfies_subset_iff ..)
  refine ⟨B, hB, ⟨fun A hA => ((hB A).mp hA).2, (hB D).mpr ⟨hD, fun _ h => h⟩, ?_, ?_⟩⟩
  · intro A hA
    obtain ⟨C, hC⟩ := KP.difference_exists_d hKP A D
    have hCX := hc .diff D A D hD ((hB A).mp hA).1 hD C hC
    exact ⟨C, (hB C).mpr ⟨hCX, fun x hx => ((hC x).mp hx).1⟩, hC⟩
  · intro A C hA hC
    obtain ⟨T, hT⟩ := KP.difference_exists_d hKP C A
    have hTX := hc .diff A C D ((hB A).mp hA).1 ((hB C).mp hC).1 hD T hT
    obtain ⟨E, hE⟩ := KP.intersection_exists_d hKP A C
    have hEX := hc .diff A T D ((hB A).mp hA).1 hTX hD E (fun x => (hE x).trans (by
      change M.mem x A ∧ M.mem x C ↔ M.mem x A ∧ ¬ M.mem x T
      rw [hT x]
      exact ⟨fun ⟨ha, hb⟩ => ⟨ha, fun h => h.2 hb⟩,
        fun ⟨ha, hn⟩ => ⟨ha, Classical.byContradiction fun hb => hn ⟨ha, hb⟩⟩⟩))
    exact ⟨E, (hB E).mpr ⟨hEX, fun x hx => ((hB A).mp hA).2 x ((hE x).mp hx).1⟩, hE⟩

/-- X 内实际存在 D→X 的代表函数：由单点集与乘积得到常值 D 的图。 -/
theorem source_function_l (hKP : M.Models KP) {X D} (hc : Rd_closed_d X) (hD : M.mem D X) :
    ∃ f, M.mem f X ∧ Fn0_d D X f := by
  obtain ⟨S, hS⟩ := rd_fun_exists_l hKP .pair D D D
  have hSX := hc .pair D D D hD hD hD S hS
  obtain ⟨f, hf⟩ := rd_fun_exists_l hKP .prod D S D
  have value {d x} (hx : Rd_entry_d d x f) : x = D := by
    obtain ⟨p, hp, hpf⟩ := hx
    obtain ⟨a, b, _, hb, hab⟩ := (hf p).mp hpf
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hab
    exact ((hS x).mp hb).elim id id
  refine ⟨f, hc .prod D S D hD hSX hD f hf, ⟨?_, ?_, fun d _ x _ y _ hx hy => (value hx).trans (value hy).symm⟩⟩
  · intro p hp
    obtain ⟨d, x, hd, hx, hp⟩ := (hf p).mp hp
    exact ⟨d, hd, x, (((hS x).mp hx).elim id id).symm ▸ hD, hp⟩
  · intro d hd
    obtain ⟨p, hp⟩ := (kp_pair_l hKP).total d D
    exact ⟨D, hD, p, hp, (hf p).mpr ⟨d, D, hd, (hS D).mpr (Or.inl rfl), hp⟩⟩

end YesMetaZFC.SetTheory.FilterZF
