import YesMetaZFC.Model.SetTheory.Internal.TypeRank
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingFinite
import YesMetaZFC.Model.SetTheory.Internal.SourceHierarchy

/-! # 像查询域覆盖新的低秩参数

名字域、有限列空间和查询对的定义依次由初等性搬运。目标中的任意实际
有限名字列只需属于目标载体，不必来自旧列的逐点像。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.type_pool_cover_l {ω θ X R Y S c d j n U U' D D' V E : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d I θ X) (hθ : M.IsLimitOrdinal θ) (hωX : M.mem ω X)
    (hY : M.TransitiveSet Y) (hm : Smem_d I c X R) (hn : Smem_d I d Y S)
    (hj : Smap_d I ω c d X Y j) (hnω : M.mem n ω) (hnj : Rd_entry_d n n j)
    (hUX : M.mem U X) (hU : Rd_entry_d U U' j) (hD : Rd_entry_d D D' j)
    (pool : Tt_pool_d I ω n U D) (pool' : Tt_pool_d I ω n V E)
    (hVU : M.MemberSubset V U') (hEY : M.MemberSubset E Y) : M.MemberSubset E D' := by
  have ht := ZF.v_transitive_l I hZF hX
  have hωj := hj.omega_l I hZF hω ht hY hm hn hωX
  obtain ⟨N, T, names, seq, prod⟩ := pool
  have hNX := names.rank_mem_l hZF hω hX hθ hωX hnω hUX
  have hTX := ZF.v_fseq_mem_l I hZF hX hθ hω hωX hNX seq
  obtain ⟨N', _, hN⟩ := hj.1.1.2.2 N hNX
  obtain ⟨T', _, hT⟩ := hj.1.1.2.2 T hTX
  -- 名字域中的新常量由 j(U) 决定，变量名仍是同一个内部 n。
  let φ : Formula 1 4 := .iff (.mem .newest (.bound 1)) (tn_name_m (.bound 3) (.bound 2) .newest)
  have tr := hj.forall_delta_l hZF hω ht hY hm hn φ (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed])
    (.iff (.mem _ _) (tn_name_delta_l ..))
    ⟨Fin.cases N (Fin.cases U (fun _ => n)), fun _ => n⟩
    ⟨Fin.cases N' (Fin.cases U' (fun _ => n)), fun _ => n⟩ (Fin.cases hN (Fin.cases hU (fun _ => hnj)))
  simp only [φ, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, tn_name_sat_l hZF.1] at tr
  have names' : ∀ a, M.mem a Y → (M.mem a N' ↔ Tn_name_d n U' a) := tr.mp (fun a _ => names a)
  -- 同一全称公式覆盖目标中的所有有限列，包括不在旧列像中的列。
  let ψ : Formula 1 4 := .iff (.mem .newest (.bound 1))
    (Formula.existsMem (.bound 3) (fn0_m .newest (.bound 3) (.bound 1)))
  have tr := hj.forall_delta_l hZF hω ht hY hm hn ψ (by simp -implicitDefEqProofs [ψ, Definitional.Formula.FreeClosed])
    (.iff (.mem _ _) (.existsMem _ (fn0_delta_l ..)))
    ⟨Fin.cases T (Fin.cases N (fun _ => ω)), fun _ => ω⟩
    ⟨Fin.cases T' (Fin.cases N' (fun _ => ω)), fun _ => ω⟩ (Fin.cases hT (Fin.cases hN (fun _ => hωj)))
  simp only [ψ, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, fn0_sat_l hZF.1] at tr
  have seq' : ∀ e, M.mem e Y → (M.mem e T' ↔ ∃ b, M.mem b ω ∧ Fn0_d b N' e) :=
    tr.mp (fun e _ => (seq e).trans (exists_congr fun b => and_congr_right fun _ =>
      ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩))
  let χ : Formula 1 4 := .iff (.mem .newest (.bound 1)) (Formula.existsMem (.bound 3)
    (Formula.existsMem (.bound 3) (kpair0_m (.bound 2) (.bound 1) .newest)))
  have tr := hj.forall_delta_l hZF hω ht hY hm hn χ (by simp -implicitDefEqProofs [χ, Definitional.Formula.FreeClosed])
    (.iff (.mem _ _) (.existsMem _ (.existsMem _ (kpair0_delta_l ..))))
    ⟨Fin.cases D (Fin.cases T (fun _ => ω)), fun _ => ω⟩
    ⟨Fin.cases D' (Fin.cases T' (fun _ => ω)), fun _ => ω⟩ (Fin.cases hD (Fin.cases hT (fun _ => hωj)))
  simp only [χ, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, kpair0_sat_l hZF.1] at tr
  have prod' : ∀ p, M.mem p Y → (M.mem p D' ↔ ∃ z, M.mem z ω ∧ ∃ e, M.mem e T' ∧ KPair_d M p z e) :=
    tr.mp (fun p _ => prod p)
  obtain ⟨N₀, T₀, names₀, seq₀, prod₀⟩ := pool'
  intro p hp
  have hpY := hEY p hp
  obtain ⟨z, hz, e, he, code⟩ := (prod₀ p).mp hp
  have heY := (code.mem_l M hY hpY).2
  obtain ⟨b, hb, fn⟩ := (seq₀ e).mp he
  have name_image a i (hia : Rd_entry_d i a e) : M.mem a N' := by
    obtain ⟨q, hq, hqe⟩ := hia
    have haY := (hq.mem_l M hY (hY e heY q hqe)).2
    apply (names' a haY).mpr
    rcases (names₀ a).mp (fn.output_mem_of_pairMember ⟨q, hq, hqe⟩) with ha | ha | ⟨x, hx, pair⟩
    · exact Or.inl ha
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr ⟨x, hVU x hx, pair⟩)
  have fn' : M.IsSetFunctionFromTo I e b N' := ⟨fn.1, fn.2.1,
    fun i hi => (fn.2.2 i hi).imp fun a ha => ⟨name_image a i ha.2, ha.2⟩⟩
  exact (prod' p hpY).mpr ⟨z, hz, e, (seq' e heY).mpr ⟨b, hb, fn0_of_function_l (ZF.modelsKP hZF) fn'⟩, code⟩

/-- 目标覆盖 V_L 且 L≤j(κ) 时，j(Vκ) 包含整个实际 V_L。 -/
theorem Smap_d.type_constants_cover_l {ω θ X R Y S c d j κ κ' B U U' L V : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d I θ X) (hθ : M.IsLimitOrdinal θ) (hκ : M.mem κ θ)
    (hY : M.TransitiveSet Y) (hm : Smem_d I c X R) (hn : Smem_d I d Y S)
    (hj : Smap_d I ω c d X Y j) (hκj : Rd_entry_d κ κ' j) (hU : Rd_entry_d U U' j)
    (hB : V_d I κ B) (hBU : M.MemberSubset B U) (hV : V_d I L V)
    (cover : M.MemberSubset V Y) (bound : M.MemberSubset L κ') : M.MemberSubset V U' := by
  classical
  have ht := ZF.v_transitive_l I hZF hX
  have hBX := ZF.v_mem_l I hZF hB hX hκ
  obtain ⟨B', hB'Y, hBB⟩ := hj.1.1.2.2 B hBX
  obtain ⟨P, F, hP, hF, cert, _⟩ := vr_source_l hZF hX hθ hκ hB
  have rank : Vr_d Y κ' B' := (hj.hierarchy_l hZF hω ht hY hm hn hκj hBB).mp
    ⟨P, F, hP, hF, fun t _ => cert t⟩
  have hκ' := hj.ordinal_l hZF hω ht hY hm hn hκj (hθ.1.mem hκ)
  have hκ'Y := hj.1.1.output_mem_of_pairMember hκj
  have hLY : M.mem L Y := by
    by_cases eq : L = κ'
    · exact eq ▸ hκ'Y
    · exact hY κ' hκ'Y L (Structure.IsOrdinal.mem_of_properSubset hZF.1 (v_ordinal_l I hV) hκ'
        ⟨bound, fun hh => eq (hZF.1.eq_of_same_members L κ' hh)⟩ (KP.difference_exists_d (ZF.modelsKP hZF) L κ'))
  have hierarchy := (sc_hierarchy_iff_l hZF hω ht hY hm hn hj).mp (sc_v_hierarchy_l hZF hθ hX)
  obtain ⟨W, hWY, hW⟩ := hierarchy L hLY (v_ordinal_l I hV)
  have eq := vr_agree_l hZF hY hWY hV cover hW
  subst W
  have sub := (rank.compare_l hZF hY hB'Y hWY hW bound).1
  have into := (hj.subset_l hZF hω ht hY hm hn hBB hU).mp hBU
  exact fun x hx => into x (sub x hx)

end YesMetaZFC.SetTheory.Internal
