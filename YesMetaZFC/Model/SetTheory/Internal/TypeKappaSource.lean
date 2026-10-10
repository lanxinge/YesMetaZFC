import YesMetaZFC.Model.SetTheory.Internal.TypeDomain
import YesMetaZFC.Model.SetTheory.Internal.FlatTypePredecessor

/-! # 前一秩层中 κ 型的完整原公式

公式自行求出 Vδ、Vκ、常量域和全部查询域；输入仅有 ω、κ、δ、元数、
平坦元组及类型候选。解码、查询域与真值始终保持原编码。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def tf_kappa_s : UnarySchema 5 where
  body := set[6] ⟪∃ Z B, ⌜v_m FlatPairing.convention⌝ₚ(⌜(.bound 3 : Term 6)⌝ₛ, Z) ∧
    ⌜v_m FlatPairing.convention⌝ₚ(⌜(.bound 4 : Term 6)⌝ₛ, B) ∧
    (∃ U ∈ Z, ∃ D ∈ Z, ⌜tt_constants0_m⌝ₚ(⌜(.bound 4 : Term 6)⌝ₛ, B, U) ∧
      ⌜tt_pool0_m⌝ₚ(⌜(.bound 5 : Term 6)⌝ₛ, Z, ⌜(.bound 2 : Term 6)⌝ₛ, U, D) ∧
      ⌜tf_type_m⌝ₚ(⌜(.bound 5 : Term 6)⌝ₛ, ⌜(.bound 3 : Term 6)⌝ₛ, ⌜(.bound 2 : Term 6)⌝ₛ,
        ⌜(.bound 1 : Term 6)⌝ₛ, D, ⌜(.newest : Term 6)⌝ₛ))⟫

def tf_kappa_m {d} (ω κ δ n h t : Term d) : Formula 1 d :=
  pred_m tf_kappa_s (Fin.cases h (Fin.cases n (Fin.cases δ (Fin.cases κ (fun _ => ω))))) t
@[simp] theorem tf_kappa_closed_l {d} (ω κ δ n h t : Term d)
    (hw : ω.freeSupport = []) (hk : κ.freeSupport = []) (hd : δ.freeSupport = [])
    (hn : n.freeSupport = []) (hh : h.freeSupport = []) (ht : t.freeSupport = []) :
    (tf_kappa_m ω κ δ n h t).FreeClosed :=
  pred_m_freeClosed tf_kappa_s _ _ (Fin.cases hh (Fin.cases hn (Fin.cases hd (Fin.cases hk (fun _ => hw))))) ht

variable (hZF : M.Models ZF) {ω ν μ X Y : M.Domain} (hω : M.IsOmega ω)
  (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) ν X) (hW : V_d (kp_pair_l (ZF.modelsKP hZF)) μ Y)
  (hs : M.SuccessorOf μ ν) (hωY : M.mem ω Y)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "N₀" => rt_model_l Y (Nonempty.intro (Subtype.mk ω hωY))
local notation "J" => fp_rank_interpretation_l Q hZF hω hW hωY

include hω hV hW hs in
private theorem tf_kappa_values_l (κ δ n h t : (N₀).Domain) {Z B U D c R s : M.Domain}
    (hZ : V_d Q δ.val Z) (hδ : M.IsLimitOrdinal δ.val) (hωδ : M.mem ω δ.val) (hκδ : M.mem κ.val δ.val)
    (hB : V_d Q κ.val B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ.val)
    (pool : Tt_pool_d Q ω n.val U D) (hm : Smem_d Q c X R) (hn : M.mem n.val ω)
    (tuple : Fn0_d n.val X s) (point : M.mem δ.val X) (agree : Sx_graph_d Q K s h.val) :
    Formula.satisfies (⟨Fin.cases t (Fin.cases h (Fin.cases n (Fin.cases δ (Fin.cases κ
      (fun _ => ⟨ω, hωY⟩))))), fun _ => h⟩ : Env N₀ 6) tf_kappa_s.body ↔ Tt_truth_d Q ω c n.val s δ.val D t.val := by
  let ρ : Env N₀ 6 := ⟨Fin.cases t (Fin.cases h (Fin.cases n (Fin.cases δ (Fin.cases κ
    (fun _ => ⟨ω, hωY⟩))))), fun _ => h⟩
  have trans := ZF.v_transitive_l Q hZF hW
  have hδν := ZF.v_ordinal_height_l hZF hV hδ.1 point
  have hZX := ZF.v_mono_l Q hZF hZ hV ((v_ordinal_l Q hV).transitive δ.val hδν)
  have hUZ := tt_constants_rank_l hZF hZ hδ hκδ hB constants
  have hDZ := pool.rank_mem_l hZF hω hZ hδ (ZF.v_ordinal_mem_l Q hZF hZ hωδ) hn hUZ
  have ux : M.MemberSubset U X := fun x hx => hZX x (ZF.v_transitive_l Q hZF hZ U hUZ x hx)
  have const (A C U' D' : (N₀).Domain) :
      Formula.satisfies ((((ρ.push A).push C).push U').push D') (tt_constants0_m (.bound 8) (.bound 2) (.bound 1)) ↔
      ∀ x, M.mem x U'.val ↔ M.mem x C.val ∨ x = κ.val :=
    (rt_model_delta_l trans _ (tt_constants0_delta_l ..) _).trans
      (tt_constants0_sat_l hZF.1 (image_env_l (M := N₀) (N := M) Subtype.val ((((ρ.push A).push C).push U').push D')) ..)
  have pools (A C U' D' : (N₀).Domain) (ha : V_d Q δ.val A.val) (hu : M.mem U'.val A.val) :
      Formula.satisfies ((((ρ.push A).push C).push U').push D') (tt_pool0_m (.bound 9) (.bound 3) (.bound 6) (.bound 1) .newest) ↔
        Tt_pool_d Q ω n.val U'.val D'.val :=
    (rt_model_delta_l trans _ (tt_pool0_delta_l ..) _).trans
      (tt_pool0_rank_l hZF (image_env_l (M := N₀) (N := M) Subtype.val ((((ρ.push A).push C).push U').push D'))
        (.bound 9) (.bound 3) (.bound 6) (.bound 1) .newest hω ha hδ (ZF.v_ordinal_mem_l Q hZF ha hωδ) hn hu)
  have types (A C U' D' : (N₀).Domain) (eq : D'.val = D) :
      Formula.satisfies ((((ρ.push A).push C).push U').push D')
        (tf_type_m (.bound 9) (.bound 7) (.bound 6) (.bound 5) .newest (.bound 4)) ↔ Tt_truth_d Q ω c n.val s δ.val D t.val :=
    (tf_type_source_l hZF hω hV hW hs hωY ((((ρ.push A).push C).push U').push D')
      (.bound 9) (.bound 7) (.bound 6) (.bound 5) .newest (.bound 4) rfl hZ hδ hωδ hm hn tuple point ux
        (eq.symm ▸ pool) (eq.symm ▸ hDZ) agree).trans (eq ▸ Iff.rfl)
  simp only [tf_kappa_s, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    v_sat_l J (rt_model_ext_l hZF.1 trans _), Formula.satisfies_existsMem_iff]
  constructor
  · rintro ⟨A, C, ha, hc, U', hu, D', hd, constants', pool', truth⟩
    have ha' := (rt_fp_v_l Q hZF hω hW hωY hV hs δ A).mp ha
    have hc' := (rt_fp_v_l Q hZF hω hW hωY hV hs κ C).mp hc
    have eqC := ZF.v_unique_l Q hZF hc' hB
    have cu := eqC ▸ (const A C U' D').mp constants'
    have eqU := hZF.1.eq_of_same_members U'.val U (fun x => (cu x).trans (constants x).symm)
    have pp := (pools A C U' D' ha' hu).mp pool'
    have eqD := (eqU ▸ pp).unique_l hZF.1 Q pool
    exact (types A C U' D' eqD).mp truth
  · intro truth
    let A : (N₀).Domain := ⟨Z, ZF.v_mem_l Q hZF hZ hW ((hs δ.val).mpr (Or.inl hδν))⟩
    let C : (N₀).Domain := ⟨B, ZF.v_mem_l Q hZF hB hW
      ((hs κ.val).mpr (Or.inl ((v_ordinal_l Q hV).transitive δ.val hδν κ.val hκδ)))⟩
    let U' : (N₀).Domain := ⟨U, trans Z A.property U hUZ⟩
    let D' : (N₀).Domain := ⟨D, trans Z A.property D hDZ⟩
    exact ⟨A, C, (rt_fp_v_l Q hZF hω hW hωY hV hs δ A).mpr hZ,
      (rt_fp_v_l Q hZF hω hW hωY hV hs κ C).mpr hB, U', hUZ, D', hDZ,
      (const A C U' D').mpr constants, (pools A C U' D' hZ hUZ).mpr pool, (types A C U' D' rfl).mpr truth⟩

include hω hV hW hs in
theorem tf_kappa_source_l {d} (ρ : Env N₀ d) (w κ δ n h t : Term d) (hw : w.eval ρ = ⟨ω, hωY⟩)
    {Z B U D c R s : M.Domain} (hZ : V_d Q (δ.eval ρ).val Z) (hδ : M.IsLimitOrdinal (δ.eval ρ).val)
    (hωδ : M.mem ω (δ.eval ρ).val) (hκδ : M.mem (κ.eval ρ).val (δ.eval ρ).val)
    (hB : V_d Q (κ.eval ρ).val B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = (κ.eval ρ).val)
    (pool : Tt_pool_d Q ω (n.eval ρ).val U D) (hm : Smem_d Q c X R) (hn : M.mem (n.eval ρ).val ω)
    (tuple : Fn0_d (n.eval ρ).val X s) (point : M.mem (δ.eval ρ).val X)
    (agree : Sx_graph_d Q K s (h.eval ρ).val) : Formula.satisfies ρ (tf_kappa_m w κ δ n h t) ↔
      Tt_truth_d Q ω c (n.eval ρ).val s (δ.eval ρ).val D (t.eval ρ).val := by
  have env : (Definitional.Env.substitute ρ (Fin.cases t (Fin.cases h (Fin.cases n (Fin.cases δ (Fin.cases κ (fun _ => w))))))).bound =
      (⟨Fin.cases (t.eval ρ) (Fin.cases (h.eval ρ) (Fin.cases (n.eval ρ) (Fin.cases (δ.eval ρ)
        (Fin.cases (κ.eval ρ) (fun _ => ⟨ω, hωY⟩))))), fun _ => h.eval ρ⟩ : Env N₀ 6).bound := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => hw))))) i
  exact (Formula.satisfies_bind _ _ _).trans ((Formula.closed_env_l tf_kappa_s.body tf_kappa_s.freeClosed env).trans
    (tf_kappa_values_l hZF hω hV hW hs hωY (κ.eval ρ) (δ.eval ρ) (n.eval ρ) (h.eval ρ) (t.eval ρ)
      hZ hδ hωδ hκδ hB constants pool hm hn tuple point agree))

end YesMetaZFC.SetTheory.Internal
