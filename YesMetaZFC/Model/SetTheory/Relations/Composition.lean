import YesMetaZFC.Model.SetTheory.ReducedPower.SourceComposition
import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.Model.SetTheory.Relations.SeparationSource
import YesMetaZFC.Model.SetTheory.Embedding.Range

/-! # 原关系模型内部的函数复合

复合图直接在当前原结构的定义域和值域乘积中分离。
所得函数码仍属于同一原关系载体，随后才沿坐标图读取背景代表。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_compose_raw_l {ω c' Y S : M.Domain}
    (hω : M.IsOmega ω) (model : Smdl_d I c' Y S) (theory : Sc_theory_d I ω Y S)
    (en : Extensional (smdl_structure_l I (R := S) model.2.1))
    (A B C t f : (smdl_structure_l I (R := S) model.2.1).Domain)
    (ft : Fn0_d A B t) (ff : Fn0_d B C f) :
    ∃ g : (smdl_structure_l I (R := S) model.2.1).Domain, Cp0_d A B C t f g := by
  let N := smdl_structure_l I (R := S) model.2.1
  let ρ : Env N 0 := ⟨Fin.elim0, fun _ => A⟩
  obtain ⟨P, prod⟩ := (theory.algebra model.2.1 ρ).1.2.2.1 A C
  change Formula.satisfies (((ρ.push A).push C).push P) (ri_image_m .prod (.bound 2) (.bound 1) .newest) at prod
  simp only [ri_image_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_imp_iff, ri_value_sat_l en, ri_guard_sat_l en,
    Definitional.Term.eval_weaken] at prod
  change (∀ p, N.mem p P → ∃ x, N.mem x A ∧ ∃ z, N.mem z C ∧ KPair_d N p x z) ∧
    (∀ x, N.mem x A → ∀ z, N.mem z C → True → ∃ p, N.mem p P ∧ KPair_d N p x z) at prod
  let η : Env N 5 := ⟨Fin.cases f (Fin.cases t (Fin.cases C (Fin.cases B (fun _ => A)))), fun _ => A⟩
  let φ : UnarySchema 5 := { body := Formula.existsMem (.bound 5) (Formula.existsMem (.bound 4)
    (.conj (kpair0_m (.bound 2) (.bound 1) .newest) (Formula.existsMem (.bound 6)
      (.conj (rd_entry0_m (.bound 2) .newest (.bound 5)) (rd_entry0_m .newest (.bound 1) (.bound 4)))))) }
  have read p : φ.denote η p ↔ ∃ x, N.mem x A ∧ ∃ z, N.mem z C ∧ KPair_d N p x z ∧
      ∃ y, N.mem y B ∧ Rd_entry_d x y t ∧ Rd_entry_d y z f := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      kpair0_sat_l en, rd_entry0_sat_l en]; rfl
  obtain ⟨q, identity, _⟩ := smap_identity_l I hZF (X := Y) (c := c') hω
  obtain ⟨g₀, hg, sep⟩ := sc_separate_raw_l I hZF hω model theory model identity φ η P
  let g : N.Domain := ⟨g₀, hg⟩
  have graph x z : Rd_entry_d x z g ↔ N.mem x A ∧ N.mem z C ∧
      ∃ y, N.mem y B ∧ Rd_entry_d x y t ∧ Rd_entry_d y z f := by
    constructor
    · rintro ⟨p, pair, hp⟩
      obtain ⟨u, hu, v, hv, pv, point⟩ := (read p).mp ((sep p).mp hp).2
      obtain ⟨rfl, rfl⟩ := kpair_injective_l N pv pair
      exact ⟨hu, hv, point⟩
    · rintro ⟨hx, hz, point⟩
      obtain ⟨p, hp, pair⟩ := prod.2 x hx z hz trivial
      exact ⟨p, pair, (sep p).mpr ⟨hp, (read p).mpr ⟨x, hx, z, hz, pair, point⟩⟩⟩
  have point x (hx : N.mem x A) : ∃ y, N.mem y B ∧ ∃ z, N.mem z C ∧
      Rd_entry_d x y t ∧ Rd_entry_d y z f ∧ Rd_entry_d x z g := by
    obtain ⟨y, hy, hxy⟩ := ft.2.1 x hx
    obtain ⟨z, hz, hyz⟩ := ff.2.1 y hy
    exact ⟨y, hy, z, hz, hxy, hyz, (graph x z).mpr ⟨hx, hz, y, hy, hxy, hyz⟩⟩
  refine ⟨g, ⟨?_, ?_, ?_⟩, point⟩
  · intro p hp
    obtain ⟨x, hx, z, hz, pair, _⟩ := (read p).mp ((sep p).mp hp).2
    exact ⟨x, hx, z, hz, pair⟩
  · intro x hx
    obtain ⟨_, _, z, hz, _, _, hxz⟩ := point x hx
    exact ⟨z, hz, hxz⟩
  · intro x hx y hy z hz hxy hxz
    obtain ⟨u, hu, hxu, huy⟩ := ((graph x y).mp hxy).2.2
    obtain ⟨v, hv, hxv, hvz⟩ := ((graph x z).mp hxz).2.2
    have eq := ft.2.2 x hx u hu v hv hxu hxv
    exact ff.2.2 u hu y hy z hz huy (eq.symm ▸ hvz)

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
    (hω : M.IsOmega ω) (hm : Smdl_d I c X R)
    (theory : Sc_theory_d I ω X R) (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (ext : Rf_ext_d I Y S) (A B t : (smdl_structure_l I (R := S) model.2.1).Domain)
    (ft : Fn0_d A B t) (ff : Rf_fun_d I Y S B.val f) : ∃ g, Rf_pull_d hZF Y S A.val t.val f g := by
  have en := ext.native_l I model.2.1
  let F : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨f, ff.mem_l I⟩
  obtain ⟨C, fn⟩ := (rf_fun_native_l I model.2.1 en B F).mp ff
  obtain ⟨g, comp⟩ := sc_compose_raw_l hZF hω model (theory.map_l I hZF hω hm model hq) en A B C t F ft fn
  refine ⟨g.val, (rf_fun_native_l I model.2.1 en A g).mpr ⟨C, comp.1⟩, fun x y z hz ht => ?_⟩
  let a : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨x, (ht.bounds_l I).1⟩
  let b : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨y, (ht.bounds_l I).2.1⟩
  let v : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨z, hz⟩
  exact (rf_val_native_l I model.2.1 en a v g).trans
    ((comp.value_l ft fn ((rf_val_native_l I model.2.1 en a b t).mp ht)).trans
      (rf_val_native_l I model.2.1 en b v F).symm)

end YesMetaZFC.SetTheory.Internal
