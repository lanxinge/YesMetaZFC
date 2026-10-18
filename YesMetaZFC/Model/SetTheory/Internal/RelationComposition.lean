import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.SourceComposition
import YesMetaZFC.Model.SetTheory.Internal.RelationEvaluation

/-! # 原关系模型内部的函数复合

源内实际复合的封闭句子沿完整初等图传输，覆盖目标的新定义域和新函数。
所得函数码仍属于原关系载体，随后才沿坐标图读取背景代表。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_compose_raw_l {ω c X R c' Y S q : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (en : Extensional (smdl_structure_l I (R := S) model.2.1))
    (A B C t f : (smdl_structure_l I (R := S) model.2.1).Domain)
    (ft : Fn0_d A B t) (ff : Fn0_d B C f) :
    ∃ g : (smdl_structure_l I (R := S) model.2.1).Domain, Cp0_d A B C t f g := by
  let ψ : Formula 1 5 := .imp
    (.conj (fn0_m (.bound 4) (.bound 3) (.bound 1)) (fn0_m (.bound 3) (.bound 2) .newest))
    (.existsE (cp0_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))
  let φ : Formula 1 0 := .forallE (.forallE (.forallE (.forallE (.forallE ψ))))
  obtain ⟨z, hz⟩ := hm.1.2.1
  let ρ : Env (smdl_structure_l I (R := R) hm.1.2.1) 0 := ⟨Fin.elim0, fun _ => ⟨z, hz⟩⟩
  let η : Env (smdl_structure_l I (R := S) model.2.1) 0 := ⟨Fin.elim0, fun _ => A⟩
  have valid : Formula.satisfies ρ φ := by
    apply (smem_formula_l I hm ⟨⟨z, hz⟩⟩ φ ⟨ρ.bound, ρ.free⟩).mp
    simp only [φ, Formula.satisfies_forall_iff, ψ, Formula.satisfies_imp_iff, Formula.satisfies_exists_iff]
    intro a b c t f fn
    have fn := (rt_model_delta_l hX _ (.conj (fn0_delta_l ..) (fn0_delta_l ..)) _).mp fn
    simp only [Formula.satisfies_conj_iff, fn0_sat_l hZF.1] at fn
    obtain ⟨g, hg, comp⟩ := sc_compose_l hZF hω hX hm theory a.property b.property t.property f.property
      fn.1 (fn.2.mono_target_l (hX c.val c.property))
    refine ⟨⟨g, hg.1⟩, (rt_model_delta_l hX _ (cp0_delta_l ..) _).mpr ?_⟩
    exact (cp0_sat_l hZF.1 ..).mpr (comp.retarget_l fn.2)
  have moved := (smap_source_l I hZF hω hm.1 model hq φ
    (by simp -implicitDefEqProofs [φ, ψ, Definitional.Formula.FreeClosed]) ρ η (fun i => Fin.elim0 i)).mp valid
  simp only [φ, Formula.satisfies_forall_iff, ψ, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, fn0_sat_l en, cp0_sat_l en] at moved
  exact moved A B C t f ⟨ft, ff⟩

def Rf_pull_d (Y S d t f g : M.Domain) : Prop := Rf_fun_d I Y S d g ∧
  ∀ x y z, M.mem z Y → Rf_val_d I Y S x y t → (Rf_val_d I Y S x z g ↔ Rf_val_d I Y S y z f)

def rf_pull_m {n} (Y S d t f g : Term n) : Formula 1 n :=
  .conj (rf_fun_m (𝒞 := kpair_convention_l) Y S d g) (.forallE (.forallE (Formula.forallMem Y.weaken.weaken
    (.imp (rf_val_m (𝒞 := kpair_convention_l) Y.weaken.weaken.weaken S.weaken.weaken.weaken
      (.bound 2) (.bound 1) t.weaken.weaken.weaken)
      (.iff (rf_val_m (𝒞 := kpair_convention_l) Y.weaken.weaken.weaken S.weaken.weaken.weaken
        (.bound 2) .newest g.weaken.weaken.weaken)
        (rf_val_m (𝒞 := kpair_convention_l) Y.weaken.weaken.weaken S.weaken.weaken.weaken
          (.bound 1) .newest f.weaken.weaken.weaken))))))
derive_free_closed rf_pull_m

theorem rf_pull_sat_l {n} (ρ : Env M n) (Y S d t f g : Term n) :
    Formula.satisfies ρ (rf_pull_m Y S d t f g) ↔
      Rf_pull_d hZF (Y.eval ρ) (S.eval ρ) (d.eval ρ) (t.eval ρ) (f.eval ρ) (g.eval ρ) := by
  simp only [rf_pull_m, Rf_pull_d, Formula.satisfies_conj_iff, rf_fun_sat_l I,
    Formula.satisfies_forall_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_iff_iff, rf_val_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem rf_pull_exists_l {ω c X R c' Y S q f : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (ext : Rf_ext_d I Y S) (A B t : (smdl_structure_l I (R := S) model.2.1).Domain)
    (ft : Fn0_d A B t) (ff : Rf_fun_d I Y S B.val f) : ∃ g, Rf_pull_d hZF Y S A.val t.val f g := by
  have en := ext.native_l I model.2.1
  let F : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨f, ff.mem_l I⟩
  obtain ⟨C, fn⟩ := (rf_fun_native_l I model.2.1 en B F).mp ff
  obtain ⟨g, comp⟩ := sc_compose_raw_l hZF hω hX hm theory model hq en A B C t F ft fn
  refine ⟨g.val, (rf_fun_native_l I model.2.1 en A g).mpr ⟨C, comp.1⟩, fun x y z hz ht => ?_⟩
  let a : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨x, (ht.bounds_l I).1⟩
  let b : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨y, (ht.bounds_l I).2.1⟩
  let v : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨z, hz⟩
  exact (rf_val_native_l I model.2.1 en a v g).trans
    ((comp.value_l ft fn ((rf_val_native_l I model.2.1 en a b t).mp ht)).trans
      (rf_val_native_l I model.2.1 en b v F).symm)

end YesMetaZFC.SetTheory.Internal
