import YesMetaZFC.SetTheory.Ord.Code.Natural
import YesMetaZFC.SetTheory.KP.Ordinal

/-! # 内部自然数配对的坐标界

典范良序中的对角点先于所有具有更大第一坐标的点。
内部自然数归纳据此给出第一坐标不超过代码，供深度调度使用。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 对角点的最大坐标较小，故其代码严格小于右侧任意同第一坐标代码。 -/
theorem oc_pair_diagonal_lt_l (hZF : M.Models ZF) {ω i a b c d : M.Domain}
    (hw : M.IsOmega ω) (hi : M.mem i ω) (ha : M.mem a ω) (hb : M.mem b ω)
    (less : M.mem i a) (left : Oc_pair_d I i i c) (right : Oc_pair_d I a b d) :
    M.mem c d := by
  obtain ⟨s,p,hp,pc⟩ := left
  obtain ⟨t,q,hq,qd⟩ := right
  have ow := hw.isOrdinal (ZF.modelsKP hZF)
  obtain ⟨X,hX⟩ := ZF.exists_cartesianProduct hZF I ω ω
  obtain ⟨R,hr,ho⟩ := ZF.exists_canonicalOrdinalPairWellOrder hZF I ow hX
  obtain ⟨_,⟨F,hf,_⟩,_⟩ := ZF.wellOrderType_existsUnique hZF I ho
  have px := (hX p).mpr ⟨i,hi,i,hi,hp⟩
  have qx := (hX q).mpr ⟨a,ha,b,hb,hq⟩
  have fp := oc_at_function_l I hZF ow hr hf px pc
  have fq := oc_at_function_l I hZF ow hr hf qx qd
  obtain ⟨m,hm⟩ := Structure.IsOrdinalMaximum.exists_of_mem hZF.1 ow ha hb
  have im : M.mem i m := hm.left_mem_or_eq.elim
    (fun am => (ow.mem (hm.mem ha hb)).transitive a am i less)
    (fun eq => eq ▸ less)
  exact (hf.relation_iff_mem hZF I ho fp fq).mp
    ((hr.2.2 p q).mpr ⟨px,qx,i,i,a,b,i,m,hp,hq,Or.inl ⟨rfl,Or.inl rfl⟩,hm,Or.inl im⟩)

/-- 内部自然数配对的第一坐标不超过代码；归纳性质由实际公式分离。 -/
theorem oc_pair_left_bound_l (hZF : M.Models ZF) {ω a b c : M.Domain}
    (hw : M.IsOmega ω) (ha : M.mem a ω) (hb : M.mem b ω) (pair : Oc_pair_d I a b c) :
    M.MemberSubset a c := by
  let ρ : Env M 1 := ⟨fun _ => ω,fun _ => ω⟩
  let φ : UnarySchema 1 := { body := set[2] ⟪∀ b ∈ ⌜(.bound 1 : Term 2)⌝ₛ, ∀ c,
    ⌜(oc_pair_m (𝒞 := 𝒞))⌝ₚ(⌜(Term.newest : Term 2)⌝ₛ,b,c) →
      ⌜Formula.subset⌝ₚ(⌜(Term.newest : Term 2)⌝ₛ,c)⟫ }
  have sat x : φ.denote ρ x ↔ ∀ y, M.mem y ω → ∀ z, Oc_pair_d I x y z → M.MemberSubset x z := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_forallMem_iff,Formula.satisfies_forall_iff,
      Formula.satisfies_imp_iff,oc_pair_sat_l I hZF.1,Formula.satisfies_subset_iff,
      Definitional.Term.eval_weaken]
    rfl
  have all : ∀ x, M.mem x ω → φ.denote ρ x := by
    apply hw.induction _ (ZF.separation_exists_d hZF φ ρ ω)
    · intro e he
      exact (sat e).mpr (fun _ _ _ _ x hx => (he x hx).elim)
    · intro n hn ih m sm
      apply (sat m).mpr
      intro y hy z code
      obtain ⟨m',sm',hm⟩ := hw.1.2 n hn
      have hm : M.mem m ω := sm'.eq hZF.1 sm ▸ hm
      have on := hw.members_areOrdinals (ZF.modelsKP hZF) n hn
      obtain ⟨d,nd⟩ := oc_pair_exists_l I hZF on on
      have sub := (sat n).mp ih n hn d nd
      have dz := oc_pair_diagonal_lt_l I hZF hw hn hm hy sm.predecessor_mem nd code
      have oz := (oc_pair_types_l I hZF code).2.2
      have nz := ordinal_down_l (ZF.modelsKP hZF) on oz sub dz
      intro x hx
      rcases (sm x).mp hx with hx | eq
      · exact oz.transitive n nz x hx
      · exact (hZF.1.eq_of_same_members x n eq).symm ▸ nz
  exact (sat a).mp (all a ha) b hb c pair

end YesMetaZFC.SetTheory
