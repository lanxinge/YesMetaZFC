import YesMetaZFC.SetTheory.LargeCardinal.Types.OneStep
import YesMetaZFC.SetTheory.LargeCardinal.Extender.CriticalPoint
import YesMetaZFC.Model.SetTheory.Types.SubtypeReboundImage
import YesMetaZFC.SetTheory.LargeCardinal.Types.ImageSyntax
import YesMetaZFC.Model.SetTheory.Types.SubtypeUp
import YesMetaZFC.Model.SetTheory.Types.ExceedsSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Types.ElasticNumericTransfer
import YesMetaZFC.Model.SetTheory.Types.DropEmbedding

/-! # 一步伸展中的实际像子类型

按给定历史界读取伸展证书中的同一超幂。原投影查询先进入类型集合的像，
随后统一更换上域参数为实际 j(κ)；支撑界保证候选域严格低于 j(κ)。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ee_one_step_d.image_l {ω κ δ n u τ m w b a z B U D η A c₀ R₀ r χ : M.Domain}
    {σ : Fin 7 → M.Domain} {q : Ee_queries_d M}
    (hω : M.IsOmega ω) (hδ : M.IsLimitOrdinal δ)
    (prog : Ts_program_d hZF ω n b σ a z) (language : Ee_language_d hZF ω κ n B U D q)
    (hA : V_d I η A) (model : Smem_d I c₀ A R₀) (type : Tt_realized_d I ω c₀ A R₀ n r δ U D u)
    (hτ : M.IsLimitOrdinal τ) (hmm : M.mem m ω) (hχ : M.mem χ δ)
    (step : Ee_one_step_d hZF ω κ δ n u τ m w b σ z) :
    ∃ X K R L F c d Y S j κ' U' D' u', V_d I δ X ∧ Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R ∧
      M.mem L δ ∧ M.mem κ L ∧ M.mem τ L ∧ M.mem χ L ∧ It_local_d I ω X R κ L F ∧ Sc_inaccessible_d ω X L ∧
      Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X F ∧ Smem_d I c X R ∧ Smem_d I d Y S ∧ It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c d j ∧
      Wd_crit_d I X j κ κ' ∧ M.MemberSubset L κ' ∧ M.IsLimitOrdinal κ' ∧
      Rd_entry_d U U' j ∧ Rd_entry_d D D' j ∧ Rd_entry_d u u' j ∧ Tt_pool_d I ω n U' D' ∧
      Ts_subtype_d ω n κ' τ m U' w b σ z u' := by
  obtain ⟨ℓ, X, K, R, L, F, C, V, Q, v, _, hℓ, hτℓ, _, hX, source, hLδ, hκL, hℓL,
    hχL, loc, inacc, strength, _, _, _, stretch, subtype⟩ := step χ hχ
  obtain ⟨c, d, Y, S, j, u', mx, my, ultra, huu, cut⟩ := stretch
  have hj := ultra.elementary_l hZF mx.1 my.1
  have hY := ultra.transitive_l hZF my.1
  have theory := source.theory.map_l I hZF hω mx.1 my.1 hj
  have hκδ := hδ.1.transitive L hLδ κ hκL
  have hUX := tt_constants_rank_l hZF hX hδ hκδ language.rank language.constants
  have hDX := language.pool.rank_mem_l (ZF.modelsKP hZF) hω hX hδ source.omega_mem prog.finite hUX
  obtain ⟨κ', _, hκj⟩ := hj.1.1.2.2 κ source.cardinal_mem
  obtain ⟨U', _, hU⟩ := hj.1.1.2.2 U hUX
  obtain ⟨D', _, hD⟩ := hj.1.1.2.2 D hDX
  have κlimit := (hj.limit_l hZF hω source.transitive hY mx my hκj).mp language.limit
  have hκU := (hj.member_l I hZF hω mx my hκj hU).mp ((language.constants κ).mpr (Or.inr rfl))
  obtain ⟨P, hP, power⟩ := sc_v_power_l (ZF.modelsKP hZF) hδ hX K source.finite.mem_l
  have family := loc.measures_l hZF source.omega (source.read_source_l hZF) source.code source.theory
    (sf_finite_power_l hZF source.omega source.transitive source.code source.theory (source.finite_l (ZF.modelsKP hZF)) hP power)
  have ord := loc.ordinals_l (ZF.modelsKP hZF) source.transitive source.code
  have bound := ultra.support_l hZF source family (loc.coherent_l hZF (source.read_source_l hZF) source.code) (loc.atoms_l hZF (source.read_source_l hZF) source.code)
    (loc.normal_l hZF (source.read_source_l hZF) source.code) ord.1 ord.2 mx my hκj
  have critical := ultra.critical_l hZF source family source (fun _ _ _ _ _ _ => Iff.rfl) loc hκL mx my hκj
  have hτL := ord.2.transitive ℓ hℓL τ hτℓ
  have sub : Ts_subtype_d ω n ℓ τ m V w b σ z u' := by
    obtain ⟨ht, nm, q₀, code, hq⟩ := subtype
    exact ⟨ht, nm, q₀, code, ((cut q₀).mp hq).2⟩
  have nat k (hk : M.mem k ω) := (tt_constants_finite_l hZF hω hk language.limit language.rank language.constants).2
  have hwU := (tt_constants_finite_l hZF hω prog.finite language.limit language.rank language.constants).1
  have image := hj.subtype_rebound_l hZF hω hX hδ source.omega_mem hY mx my theory prog hUX hU hD huu
    hA model type hwU nat hℓ κlimit hτ (bound τ hτL) hκU hmm sub
  obtain ⟨N, E, N', E', _, _, _, _, _, names, seq, product⟩ :=
    hj.type_full_l hZF hω hX hδ source.omega_mem hY mx my theory prog.finite hUX hU hD type.pool
  exact ⟨X, K, R, L, F, c, d, Y, S, j, κ', U', D', u', hX, source, hLδ, hκL, hτL, hχL,
    loc, inacc, strength, mx, my, ultra, critical, bound, κlimit, hU, hD, huu, ⟨N', E', names, seq, product⟩, image⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 继续分支的一步伸展反射句子

原超过关系与旧类型弹性产生引理 3.23 的同一扩展器。句子保留原程序，
结论是实际像上的子类型，并使同一个扩展器支撑高于指定的历史界 χ。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tc_image_m {s} (ω κ δ n U D u τ m w b z χ : Term s) (σ : Fin 7 → Term s) : Formula 1 s := set[s] ⟪
  ∃ X K R L F c d Y T j κ' U' D' u',
    ⌜ti_image_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜δ⌝ₛ, ⌜τ⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜u⌝ₛ, X, K, R, L, F, c, d, Y, T, j, κ', U', D', u') ∧
    ⌜χ⌝ₛ ∈ L ∧ ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ, ⌜n⌝ₛ, U', D') ∧
    ⌜fun ω n κ τ m U w b z u s₀ s₁ s₂ s₃ s₄ s₅ s₆ => ts_subtype_m ω n κ τ m U w b z u
      (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
      (⌜ω⌝ₛ, ⌜n⌝ₛ, κ', ⌜τ⌝ₛ, ⌜m⌝ₛ, U', ⌜w⌝ₛ, ⌜b⌝ₛ, ⌜z⌝ₛ, u',
        ⌜σ 0⌝ₛ, ⌜σ 1⌝ₛ, ⌜σ 2⌝ₛ, ⌜σ 3⌝ₛ, ⌜σ 4⌝ₛ, ⌜σ 5⌝ₛ, ⌜σ 6⌝ₛ)⟫

/-- 一次读取完整继续证书，后续原生实例不展开其具体程序。 -/
theorem tc_image_sat_l (hKP : M.Models KP) {s} (ρ : Env M s)
    (ω κ δ n U D u τ m w b z χ : Term s) (σ : Fin 7 → Term s) :
    let I := kp_pair_l hKP
    let v := fun t : Term s => t.eval ρ
    Formula.satisfies ρ (tc_image_m ω κ δ n U D u τ m w b z χ σ) ↔
    ∃ X K R L F c d Y T j κ' U' D' u',
      (V_d I (v δ) X ∧ Ep_source_d I (v ω) (v κ) K X R ∧
        M.mem L (v δ) ∧ M.mem (v κ) L ∧ M.mem (v τ) L ∧
        It_local_d I (v ω) X R (v κ) L F ∧ Sc_inaccessible_d (v ω) X L ∧ Ex_strength_d I (v ω) (v κ) L X F ∧
        Smem_d I c X R ∧ Smem_d I d Y T ∧ It_ultra_d I (v ω) (v κ) L F c d j ∧
        Wd_crit_d I X j (v κ) κ' ∧ M.MemberSubset L κ' ∧ M.IsLimitOrdinal κ' ∧
        Rd_entry_d (v U) U' j ∧ Rd_entry_d (v D) D' j ∧ Rd_entry_d (v u) u' j) ∧
      M.mem (v χ) L ∧ Tt_pool_d I (v ω) (v n) U' D' ∧
      Ts_subtype_d (v ω) (v n) κ' (v τ) (v m) U' (v w) (v b) (fun i => v (σ i)) (v z) u' := by
  intro I v
  have eta (f : Fin 7 → M.Domain) :
      (Fin.cases (f 0) (Fin.cases (f 1) (Fin.cases (f 2) (Fin.cases (f 3)
        (Fin.cases (f 4) (Fin.cases (f 5) (fun _ => f 6))))))) = f := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  simp only [tc_image_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, ti_image_sat_l hKP, tt_pool_sat_l I hKP, ts_subtype_sat_l hKP,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, tt_eval_cases_l]
  rw [eta (fun i => (σ i).eval ρ)]

-- 原二十八个输入保持位置，末项新增当前模型内的实际历史界 χ。
def tc_seed0_m : Formula 1 29 :=
  let p : Fin 29 → Term 29 := Term.bound
  set[29] ⟪
  ⌜Formula.isOmega⌝ₚ(⌜p 0⌝ₛ) ∧
  ⌜fun ω n b a z s₀ s₁ s₂ s₃ s₄ s₅ s₆ => ts_program_m ω n b a z
    (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
    (⌜p 0⌝ₛ, ⌜p 3⌝ₛ, ⌜p 14⌝ₛ, ⌜p 15⌝ₛ, ⌜p 16⌝ₛ, ⌜p 21⌝ₛ, ⌜p 22⌝ₛ, ⌜p 23⌝ₛ, ⌜p 24⌝ₛ, ⌜p 25⌝ₛ, ⌜p 26⌝ₛ, ⌜p 27⌝ₛ) ∧
  ⌜ee_language_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 1⌝ₛ, ⌜p 3⌝ₛ, ⌜p 4⌝ₛ, ⌜p 5⌝ₛ, ⌜p 6⌝ₛ, ⌜p 17⌝ₛ, ⌜p 18⌝ₛ, ⌜p 19⌝ₛ, ⌜p 20⌝ₛ) ∧
  ⌜Formula.isLimitOrdinal⌝ₚ(⌜p 8⌝ₛ) ∧ ⌜p 8⌝ₛ ∈ ⌜p 2⌝ₛ ∧ ⌜v_sigma_m⌝ₚ(⌜p 8⌝ₛ, ⌜p 10⌝ₛ) ∧
  ⌜tt_constants0_m⌝ₚ(⌜p 8⌝ₛ, ⌜p 10⌝ₛ, ⌜p 11⌝ₛ) ∧ ⌜ee_elastic_m⌝ₚ(⌜p 17⌝ₛ, ⌜p 18⌝ₛ, ⌜p 19⌝ₛ, ⌜p 20⌝ₛ, ⌜p 7⌝ₛ) ∧
  ⌜tx_exceeds_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 2⌝ₛ, ⌜p 1⌝ₛ, ⌜p 3⌝ₛ, ⌜p 5⌝ₛ, ⌜p 6⌝ₛ, ⌜p 7⌝ₛ, ⌜p 8⌝ₛ, ⌜p 9⌝ₛ, ⌜p 11⌝ₛ, ⌜p 12⌝ₛ, ⌜p 13⌝ₛ) ∧
  ⌜p 28⌝ₛ ∈ ⌜p 2⌝ₛ⟫

def tc_result0_m : Formula 1 29 := .conj (tc_image_m
  (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9)
  (.bound 13) (.bound 14) (.bound 16) (.bound 28)
  (Fin.cases (.bound 21) (Fin.cases (.bound 22) (Fin.cases (.bound 23) (Fin.cases (.bound 24)
    (Fin.cases (.bound 25) (Fin.cases (.bound 26) (fun _ => .bound 27))))))))
  (.conj (.mem (.bound 9) (.bound 0)) (tt_pool_m (.bound 0) (.bound 9) (.bound 11) (.bound 12)))

@[simp] theorem tc_seed0_closed_l : tc_seed0_m.FreeClosed := by
  simp -implicitDefEqProofs [tc_seed0_m, Definitional.Formula.FreeClosed, Fin.forall_fin_succ]
@[simp] theorem tc_result0_closed_l : tc_result0_m.FreeClosed := by
  simp -implicitDefEqProofs [tc_result0_m, tc_image_m, Definitional.Formula.FreeClosed]
  apply ts_subtype_closed_l <;> try rfl
  intro i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i

def tc_transfer_m : Formula 1 0 := Formula.forallClosure 29 (.imp tc_seed0_m tc_result0_m)

theorem tc_transfer_closed_l : tc_transfer_m.FreeClosed :=
  (Definitional.Formula.freeClosed_forallClosure _).mpr ⟨tc_seed0_closed_l, tc_result0_closed_l⟩

/-- 超过关系中的真实上层实现调用已证的一步伸展，不另设实现参数。 -/
theorem tc_transfer_true_l (hZFC : M.Models ZFC) (ε : FreeVarId → M.Domain) :
    Formula.satisfies (⟨Fin.elim0, ε⟩ : Env M 0) tc_transfer_m := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  apply (Formula.satisfies_forallClosure_iff ε _).mpr
  intro p
  simp only [tc_seed0_m, tc_result0_m, tc_image_m, Formula.satisfies_imp_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isOmega_iff, ts_program_sat_l hZF, ee_language_sat_l hZFC,
    Formula.satisfies_isLimitOrdinal_iff, Formula.satisfies_mem_iff, v_sigma_sat_l (ZF.modelsKP hZF),
    tt_constants0_sat_l hZF.1, ee_elastic_sat_l, tx_exceeds_sat_l hZF, Formula.satisfies_exists_iff,
    ti_image_sat_l (ZF.modelsKP hZF), tt_pool_sat_l I (ZF.modelsKP hZF), ts_subtype_sat_l (ZF.modelsKP hZF),
    Definitional.Term.eval_weaken, tt_eval_cases_l]
  rintro ⟨hω, prog, language, hτ, hτδ, rank, constants, elastic, exceeds, hχ⟩
  have step := ee_one_step_l hZFC hω prog language hτ hτδ rank constants elastic exceeds
  obtain ⟨_, _, η, A, c₀, R₀, r, hA, model, type, _, _, _, _, witness⟩ := exceeds
  obtain ⟨_, regular, _⟩ := sc_v_inaccessible_read_l hZF hA
    ((language.inaccessible c₀ A R₀ r (p 2) (p 7) model type).mp elastic.2.1)
  obtain ⟨_, _, _, _, _, _, _, _, _, realized, _⟩ := witness
  obtain ⟨X, K, R, L, F, c, d, Y, T, j, κ', U', D', u', hX, source, hL, hk, ht,
    hχL, loc, card, strong, mx, my, ultra, critical, bound, limit, hU, hD, hu, pool, subtype⟩ :=
    step.image_l hZF hω regular.isLimitOrdinal prog language hA model type hτ realized.finite hχ
  exact ⟨⟨X, K, R, L, F, c, d, Y, T, j, κ', U', D', u',
    ⟨hX, source, hL, hk, ht, loc, card, strong, mx, my, ultra, critical, bound, limit, hU, hD, hu⟩, hχL, pool, subtype⟩,
    realized.finite, realized.pool⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 删除末位的一步伸展在同一超幂中的实际像

源完整类型先产生自身的 dcp，实际超幂同时搬运完整类型及其投影。
目标元数独立于源元数，因而普通回答与插入 pending 的回答共用此证明。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ee_one_step_d.dcp_image_l
    {ω κ δ q n m u v τ w b a z B U D P η A c₀ R₀ r χ : M.Domain}
    {σ : Fin 7 → M.Domain} {queries : Ee_queries_d M}
    (hw : M.IsOmega ω) (hδ : M.IsLimitOrdinal δ)
    (prog : Ts_program_d hZF ω q b σ a z) (language : Ee_language_d hZF ω κ q B U D queries)
    (rank : V_d I η A) (model : Smem_d I c₀ A R₀)
    (type : Tt_realized_d I ω c₀ A R₀ n r δ U P u)
    (succ : M.SuccessorOf n q) (drop : Td_dcp_d I q n D u v)
    (hτ : M.IsLimitOrdinal τ) (hm : M.mem m ω) (hχ : M.mem χ δ)
    (step : Ee_one_step_d hZF ω κ δ q v τ m w b σ z) :
    ∃ X K R L F c d Y S j κ' U' D' u' v', V_d I δ X ∧ Ep_source_d I ω κ K X R ∧
      M.mem L δ ∧ M.mem κ L ∧ M.mem τ L ∧ M.mem χ L ∧
      It_local_d I ω X R κ L F ∧ Sc_inaccessible_d ω X L ∧ Ex_strength_d I ω κ L X F ∧
      Smem_d I c X R ∧ Smem_d I d Y S ∧ It_ultra_d I ω κ L F c d j ∧
      Wd_crit_d I X j κ κ' ∧ M.MemberSubset L κ' ∧ M.IsLimitOrdinal κ' ∧
      Rd_entry_d U U' j ∧ Rd_entry_d D D' j ∧ Rd_entry_d u u' j ∧ Tt_pool_d I ω q U' D' ∧
      Td_dcp_d I q n D' u' v' ∧ Ts_subtype_d ω q κ' τ m U' w b σ z v' := by
  obtain ⟨r₀,v₀,_,drop₀,pretype⟩ := type.dcp_l hZF hw succ language.pool
  have eq := drop₀.unique_l I hZF.1 drop
  subst v₀
  obtain ⟨X,K,R,L,F,c,d,Y,S,j,κ',U',D',v',hX,source,hLδ,hκL,hτL,hχL,
    loc,inacc,strength,mx,my,ultra,critical,bound,κlimit,hU,hD,hv,pool,subtype⟩ :=
    step.image_l hZF hw hδ prog language rank model pretype hτ hm hχ
  have hj := ultra.elementary_l hZF mx.1 my.1
  have yt := ultra.transitive_l hZF my.1
  have theory := source.theory.map_l I hZF hw mx.1 my.1 hj
  have hUX := hj.1.1.input_mem_of_pairMember hU
  have hPX := type.pool.rank_mem_l (ZF.modelsKP hZF) hw hX hδ source.omega_mem type.finite hUX
  have huX := v_subset_mem_l I hX hPX (fun x hx => ((type.truth x).mp hx).1)
  obtain ⟨u',_,hu⟩ := hj.1.1.2.2 u huX
  have fixed := hj.natural_l hZF hw source.transitive yt mx my source.omega_mem
  have drop' := (hj.type_dcp_l hZF hw source.transitive yt mx my
    (source.algebra_l (ZF.modelsKP hZF)).pair (theory.algebra_l _ (ZF.modelsKP hZF) yt my).pair
    (fixed q prog.finite) (fixed n type.finite) hD hu hv).mp drop
  exact ⟨X,K,R,L,F,c,d,Y,S,j,κ',U',D',u',v',hX,source,hLδ,hκL,hτL,hχL,
    loc,inacc,strength,mx,my,ultra,critical,bound,κlimit,hU,hD,hu,pool,drop',subtype⟩

end YesMetaZFC.SetTheory.LargeCardinal
