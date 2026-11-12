import YesMetaZFC.SetTheory.FlatPairing.Rank
import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence

/-! # 秩层内部的原平坦配对解释

标签的有界矩阵在传递源之间绝对。配对的存在见证由已经证明的秩闭包回收，
因此原参数自由公式在包含 ω 的秩层内仍解释同一个编码；无需该层满足 KP 或 ZF。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem rt_fp_tag_l {X : M.Domain} (hX : M.TransitiveSet X) (nx : Nonempty {x // M.mem x X})
    (hE : Extensional M) (ω x y : (rt_model_l X nx).Domain) (hω : M.IsOmega ω.val) (b : Bool) :
    Fp_tag_d (M := rt_model_l X nx) b ω x y ↔ Fp_tag_d b ω.val x.val y.val := by
  let ρ : Env (rt_model_l X nx) 3 := ⟨Fin.cases y (Fin.cases x (fun _ => ω)), fun _ => ω⟩
  exact (fp_tag0_sat_l (rt_model_ext_l hE hX nx) ρ b (.bound 2) (.bound 1) .newest
    (rt_omega_l hX nx hE ω hω).1).symm.trans
    ((rt_model_delta_l hX nx (fp_tag0_delta_l b (.bound 2) (.bound 1) .newest) ρ).trans
      (fp_tag0_sat_l hE _ _ _ _ _ hω.1))

theorem rt_fp_pair_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
    {ν X : M.Domain} (hV : V_d I ν X) (nx : Nonempty {x // M.mem x X})
    (ω x y p : (rt_model_l X nx).Domain) (hω : M.IsOmega ω.val) :
    Fp_pair_d (M := rt_model_l X nx) ω x y p ↔ Fp_pair_d ω.val x.val y.val p.val := by
  let N := rt_model_l X nx
  have ht := v_transitive_l I hV
  have hων := (v_ordinal_l I hV).transitive ω.val (ZF.v_ordinal_height_l hZF hV (hω.isOrdinal (ZF.modelsKP hZF)) ω.property)
  have tags (b : Bool) (A z : N.Domain) :
      (∃ a : N.Domain, N.mem a A ∧ Fp_tag_d (M := N) b ω a z) ↔
        ∃ a, M.mem a A.val ∧ Fp_tag_d b ω.val a z.val := by
    refine ⟨fun ⟨a, ha, tag⟩ => ⟨a.val, ha, (rt_fp_tag_l ht nx hZF.1 ω a z hω b).mp tag⟩, ?_⟩
    rintro ⟨a, ha, tag⟩
    let a' : N.Domain := ⟨a, ht A.val A.property a ha⟩
    exact ⟨a', ha, (rt_fp_tag_l ht nx hZF.1 ω a' z hω b).mpr tag⟩
  constructor
  · intro pair z
    constructor
    · intro hz
      let z' : N.Domain := ⟨z, ht p.val p.property z hz⟩
      exact (or_congr (tags false x z') (tags true y z')).mp ((pair z').mp hz)
    · intro hz
      have hzX : M.mem z X := by
        rcases hz with ⟨a, ha, tag⟩ | ⟨a, ha, tag⟩
        · exact tag.rank_mem_l I hZF hω hV hων (ht x.val x.property a ha)
        · exact tag.rank_mem_l I hZF hω hV hων (ht y.val y.property a ha)
      let z' : N.Domain := ⟨z, hzX⟩
      exact (pair z').mpr ((or_congr (tags false x z') (tags true y z')).mpr hz)
  · intro pair z
    exact (pair z.val).trans (or_congr (tags false x z).symm (tags true y z).symm)

/-- 原公式量化的内部 ω 唯一等于背景 ω，然后由配对绝对性恢复原编码。 -/
theorem fp_rank_code_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
    {ω ν X : M.Domain} (hω : M.IsOmega ω) (hV : V_d I ν X) (hωX : M.mem ω X)
    (nx : Nonempty {x // M.mem x X}) {d} (ρ : Env (rt_model_l X nx) d) (p x y : Term d) :
    Formula.satisfies ρ (FlatPairing.code p x y) ↔ Fp_pair_d ω (x.eval ρ).val (y.eval ρ).val (p.eval ρ).val := by
  let N := rt_model_l X nx
  have ht := v_transitive_l I hV
  have he := rt_model_ext_l hZF.1 ht nx
  let w : N.Domain := ⟨ω, hωX⟩
  have hw := rt_omega_l ht nx hZF.1 w hω
  simp only [FlatPairing.code, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isOmega_iff, fp_pair_sat_l he, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  refine ⟨?_, fun pair => ⟨w, hw, (rt_fp_pair_l I hZF hV nx w (x.eval ρ) (y.eval ρ) (p.eval ρ) hω).mpr pair⟩⟩
  rintro ⟨v, hv, pair⟩
  have eq : v = w := he.eq_of_same_members v w (fun z => ⟨hv.2 w hw.1 z, hw.2 v hv.1 z⟩)
  exact (rt_fp_pair_l I hZF hV nx w (x.eval ρ) (y.eval ρ) (p.eval ρ) hω).mp (eq ▸ pair)

/-- 包含 ω 的实际秩层自动得到原平坦配对解释，不以整个源的模型性作前提。 -/
def fp_rank_interpretation_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
    {ω ν X : M.Domain} (hω : M.IsOmega ω) (hV : V_d I ν X) (hωX : M.mem ω X) :
    FlatPairing.convention.Interpretation (rt_model_l X ⟨⟨ω, hωX⟩⟩) where
  Codes p x y := Fp_pair_d ω x.val y.val p.val
  realizes := fp_rank_code_l I hZF hω hV hωX ⟨⟨ω, hωX⟩⟩
  total x y := by
    obtain ⟨p, hp⟩ := fp_pair_exists_l (ZF.modelsKP hZF) hω.1 x.val y.val
    have hων := (v_ordinal_l I hV).transitive ω (ZF.v_ordinal_height_l hZF hV (hω.isOrdinal (ZF.modelsKP hZF)) hωX)
    exact ⟨⟨p, hp.rank_mem_l I hZF hω hV hων x.property y.property⟩, hp⟩
  unique := fun hp hq => Subtype.ext (hp.unique_l hZF.1 hq)
  injective := by
    intro p x y u v hp hq
    obtain ⟨hx, hy⟩ := hp.injective_l (ZF.modelsKP hZF) hω.1 (hω.members_areOrdinals (ZF.modelsKP hZF)) hq
    exact ⟨Subtype.ext hx, Subtype.ext hy⟩

end YesMetaZFC.SetTheory.Internal
