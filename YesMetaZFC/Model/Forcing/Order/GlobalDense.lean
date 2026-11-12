import YesMetaZFC.Model.Forcing.Proper.Master.Syntax

/-! # 将局部稠密要求扩充为全局稠密集

在 p 以下保留原稠密集，并加入所有与 p 不相容的正条件。
包含 p 的滤子命中这个全局稠密集时，只能命中原要求。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
include hZF

theorem dense_globalize_l {B R z p D : M.Domain} (O : Cond_order_d M B R z)
    (hp : M.mem p B) (dense : Dense_d M B R z (fun q => M.mem q D) p) :
    ∃ E, Dense_set_d M B R z E ∧ ∀ q, M.mem q E ↔ M.mem q B ∧ q ≠ z ∧
      (¬ Cmp_d M B R z q p ∨ Entry_d M q p R ∧ M.mem q D) := by
  let ρ : Env M 5 := ⟨fun i => [B,R,z,p,D].get i,fun _ => B⟩
  let φ : UnarySchema 5 := { body := set[6] ⟪
    ⌜(.newest : Term 6)⌝ₛ ≠ ⌜(.bound 3 : Term 6)⌝ₛ ∧
      (¬ ⌜cmp_m⌝ₚ(⌜(.bound 1 : Term 6)⌝ₛ,⌜(.bound 2 : Term 6)⌝ₛ,⌜(.bound 3 : Term 6)⌝ₛ,
        ⌜(.newest : Term 6)⌝ₛ,⌜(.bound 4 : Term 6)⌝ₛ) ∨
       (⌜entry_m⌝ₚ(⌜(.newest : Term 6)⌝ₛ,⌜(.bound 4 : Term 6)⌝ₛ,⌜(.bound 2 : Term 6)⌝ₛ) ∧
         ⌜(.newest : Term 6)⌝ₛ ∈ ⌜(.bound 5 : Term 6)⌝ₛ))⟫ }
  have sat q : φ.denote ρ q ↔ q ≠ z ∧ (¬ Cmp_d M B R z q p ∨ Entry_d M q p R ∧ M.mem q D) := by
    simp only [UnarySchema.denote,φ,Formula.satisfies_conj_iff,Formula.extensionalNe,Formula.satisfies_neg_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1,Formula.satisfies_disj_iff,cmp_sat_l M hZF.1,
      entry_sat_l M hZF.1,Formula.satisfies_mem_iff]
    rfl
  obtain ⟨E,sep⟩ := ZF.separation_exists_d hZF φ ρ B
  have members q := (sep q).trans (and_congr_right fun _ => sat q)
  refine ⟨E,⟨fun q hq => ⟨((members q).mp hq).1,((members q).mp hq).2.1⟩,?_⟩,members⟩
  intro q hq nz
  rcases Classical.em (Cmp_d M B R z q p) with ⟨r,rq,rp⟩ | no
  · obtain ⟨s,sr,sD⟩ := dense r ⟨rq.1,rq.2.1,rp⟩
    exact ⟨s,below_trans_l O hq sr rq,(members s).mpr ⟨sr.1,sr.2.1,
      Or.inr ⟨O.trans s r p sr.1 rq.1 hp sr.2.2 rp,sD⟩⟩⟩
  · exact ⟨q,below_refl_l O hq nz,(members q).mpr ⟨hq,nz,Or.inl no⟩⟩

/-- 命中局部稠密集时同时留在指定泛型条件以下；不要求稠密集向下闭合。 -/
theorem Generic_d.meets_below_l {B R z p D : M.Domain} {G : M.Domain → Prop}
    (O : Cond_order_d M B R z) (generic : Generic_d M B R z G) (hp : G p)
    (dense : Dense_d M B R z (fun q => M.mem q D) p) :
    ∃ q, G q ∧ M.mem q D ∧ Entry_d M q p R := by
  obtain ⟨E,global,read⟩ := dense_globalize_l hZF O (generic.proper p hp).1 dense
  obtain ⟨q,hq,qE⟩ := generic.meets p hp E
    (fun r hr => global.2 r hr.1 hr.2.1)
  rcases ((read q).mp qE).2.2 with no | hit
  · obtain ⟨r,hr,rq,rp⟩ := generic.directed q p hq hp
    exact (no ⟨r,⟨(generic.proper r hr).1,(generic.proper r hr).2,rq⟩,rp⟩).elim
  · exact ⟨q,hq,hit.2,hit.1⟩

/-- 地条件属于原泛型，当且仅当它与原泛型的每个条件相容。 -/
theorem Generic_d.mem_iff_compatible_l {B R z p : M.Domain} {G : M.Domain → Prop}
    (O : Cond_order_d M B R z) (generic : Generic_d M B R z G) (hp : M.mem p B) :
    G p ↔ ∀ q, G q → Cmp_d M B R z q p := by
  constructor
  · intro gp q gq
    obtain ⟨r,gr,rq,rp⟩ := generic.directed q p gq gp
    exact ⟨r,⟨(generic.proper r gr).1,(generic.proper r gr).2,rq⟩,rp⟩
  · intro compatible
    obtain ⟨D,dense,read⟩ := dense_globalize_l hZF O hp
      (fun q hq => ⟨q,below_refl_l O hq.1 hq.2.1,hq.1⟩)
    obtain ⟨a,ga⟩ := generic.inhabited
    obtain ⟨q,gq,hq⟩ := generic.meets a ga D (fun r hr => dense.2 r hr.1 hr.2.1)
    rcases ((read q).mp hq).2.2 with no | below
    · exact (no (compatible q gq)).elim
    · exact generic.upward q p gq hp below.1

end YesMetaZFC.Model.Forcing.Internal
