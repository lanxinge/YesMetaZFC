import YesMetaZFC.SetTheory.LargeCardinal.TypeStretchQuality
import YesMetaZFC.Model.SetTheory.Internal.TypeKappaSource

/-! # 弹性中的一个任意目标高度

公式自行量化扩展器、目标常量域、查询域和目标类型。原 κ 型仅作为待伸展
集合传入；所有候选扩展器均由自身的原判断构造实际超幂。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ee_step_d (hZF : M.Models ZF) (ω κ δ n s c X R t τ : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ L F B U D v, M.mem L δ ∧ M.mem κ L ∧ M.mem τ L ∧ V_d I τ B ∧
    (∀ x, M.mem x U ↔ M.mem x B ∨ x = τ) ∧ Tt_pool_d I ω n U D ∧ Tt_truth_d I ω c n s δ D v ∧
    It_local_d ω X κ L F ∧ Sc_inaccessible_d ω X L ∧ Ex_strength_d hZF ω κ L X F ∧
    Et_stretch_d hZF ω κ L F X R t D v

def ee_step_s : UnarySchema 7 where
  body := set[8] ⟪∃ L ∈ ⌜(.bound 5 : Term 8)⌝ₛ, ∃ F ∈ ⌜(.bound 2 : Term 8)⌝ₛ,
    ∃ B ∈ ⌜(.bound 2 : Term 8)⌝ₛ, ∃ U ∈ ⌜(.bound 2 : Term 8)⌝ₛ,
    ∃ D ∈ ⌜(.bound 2 : Term 8)⌝ₛ, ∃ v ∈ ⌜(.bound 2 : Term 8)⌝ₛ,
      ⌜(.bound 6 : Term 8)⌝ₛ ∈ L ∧ ⌜(.newest : Term 8)⌝ₛ ∈ L ∧
      ⌜v_m FlatPairing.convention⌝ₚ(⌜(.newest : Term 8)⌝ₛ, B) ∧
      ⌜tt_constants0_m⌝ₚ(⌜(.newest : Term 8)⌝ₛ, B, U) ∧
      ⌜tt_pool0_m⌝ₚ(⌜(.bound 7 : Term 8)⌝ₛ, ⌜(.bound 2 : Term 8)⌝ₛ, ⌜(.bound 4 : Term 8)⌝ₛ, U, D) ∧
      ⌜tf_kappa_m⌝ₚ(⌜(.bound 7 : Term 8)⌝ₛ, ⌜(.newest : Term 8)⌝ₛ, ⌜(.bound 5 : Term 8)⌝ₛ,
        ⌜(.bound 4 : Term 8)⌝ₛ, ⌜(.bound 3 : Term 8)⌝ₛ, v) ∧
      ⌜et_quality_m⌝ₚ(⌜(.bound 7 : Term 8)⌝ₛ, ⌜(.bound 6 : Term 8)⌝ₛ, L, ⌜(.bound 2 : Term 8)⌝ₛ,
        F, ⌜(.bound 1 : Term 8)⌝ₛ, D, v)⟫

def ee_step_m {d} (ω κ δ n h X t τ : Term d) : Formula 1 d :=
  pred_m ee_step_s (Fin.cases t (Fin.cases X (Fin.cases h (Fin.cases n (Fin.cases δ (Fin.cases κ (fun _ => ω))))))) τ
@[simp] theorem ee_step_closed_l {d} (ω κ δ n h X t τ : Term d)
    (hw : ω.freeSupport = []) (hk : κ.freeSupport = []) (hd : δ.freeSupport = []) (hn : n.freeSupport = [])
    (hh : h.freeSupport = []) (hx : X.freeSupport = []) (ht : t.freeSupport = []) (hr : τ.freeSupport = []) :
    (ee_step_m ω κ δ n h X t τ).FreeClosed := pred_m_freeClosed ee_step_s _ _
      (Fin.cases ht (Fin.cases hx (Fin.cases hh (Fin.cases hn (Fin.cases hd (Fin.cases hk (fun _ => hw))))))) hr

variable (hZFC : M.Models ZFC) {ω ν μ A Y : M.Domain} (hω : M.IsOmega ω)
  (hA : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ν A)
  (hY : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) μ Y)
  (hs : M.SuccessorOf μ ν) (hωY : M.mem ω Y)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "K₀" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "N₀" => rt_model_l Y (Nonempty.intro (Subtype.mk ω hωY))
local notation "J" => fp_rank_interpretation_l I hZF hω hY hωY

include hω hA hY hs in
private theorem ee_step_values_l (κ δ n h Z t τ : (N₀).Domain) {K R B₀ U₀ Q c S s : M.Domain}
    (source : Ep_source_d hZF ω κ.val K Z.val R) (hZ : V_d I δ.val Z.val)
    (hδ : M.IsLimitOrdinal δ.val) (hωδ : M.mem ω δ.val) (hτδ : M.mem τ.val δ.val)
    (hB₀ : V_d I κ.val B₀) (constants₀ : ∀ x, M.mem x U₀ ↔ M.mem x B₀ ∨ x = κ.val)
    (pool₀ : Tt_pool_d I ω n.val U₀ Q) (sub : M.MemberSubset t.val Q)
    (hm : Smem_d I c A S) (hn : M.mem n.val ω) (tuple : Fn0_d n.val A s) (point : M.mem δ.val A)
    (agree : Sx_graph_d I K₀ s h.val) :
    ee_step_s.denote (⟨Fin.cases t (Fin.cases Z (Fin.cases h (Fin.cases n (Fin.cases δ (Fin.cases κ
      (fun _ => ⟨ω, hωY⟩)))))), fun _ => h⟩ : Env N₀ 7) τ ↔ Ee_step_d hZF ω κ.val δ.val n.val s c Z.val R t.val τ.val := by
  let ρ := (⟨Fin.cases t (Fin.cases Z (Fin.cases h (Fin.cases n (Fin.cases δ (Fin.cases κ
    (fun _ => ⟨ω, hωY⟩)))))), fun _ => h⟩ : Env N₀ 7).push τ
  let η (L F B U D v : (N₀).Domain) := ((((((ρ.push L).push F).push B).push U).push D).push v)
  have trans := ZF.v_transitive_l I hZF hY
  have const (L F B U D v : (N₀).Domain) :
      Formula.satisfies (η L F B U D v) (tt_constants0_m (.bound 6) (.bound 3) (.bound 2)) ↔
        ∀ x, M.mem x U.val ↔ M.mem x B.val ∨ x = τ.val :=
    (rt_model_delta_l trans _ (tt_constants0_delta_l ..) _).trans
      (tt_constants0_sat_l hZF.1 (image_env_l (M := N₀) (N := M) Subtype.val (η L F B U D v)) ..)
  have pools (L F B U D v : (N₀).Domain) (hu : M.mem U.val Z.val) :
      Formula.satisfies (η L F B U D v) (tt_pool0_m (.bound 13) (.bound 8) (.bound 10) (.bound 2) (.bound 1)) ↔
        Tt_pool_d I ω n.val U.val D.val :=
    (rt_model_delta_l trans _ (tt_pool0_delta_l ..) _).trans
      (tt_pool0_rank_l hZF (image_env_l (M := N₀) (N := M) Subtype.val (η L F B U D v))
        (.bound 13) (.bound 8) (.bound 10) (.bound 2) (.bound 1) hω hZ hδ
        (ZF.v_ordinal_mem_l I hZF hZ hωδ) hn hu)
  have types (L F B U D v : (N₀).Domain) (hb : V_d I τ.val B.val)
      (hc : ∀ x, M.mem x U.val ↔ M.mem x B.val ∨ x = τ.val) (hp : Tt_pool_d I ω n.val U.val D.val) :
      Formula.satisfies (η L F B U D v) (tf_kappa_m (.bound 13) (.bound 6) (.bound 11) (.bound 10) (.bound 9) .newest) ↔
        Tt_truth_d I ω c n.val s δ.val D.val v.val :=
    tf_kappa_source_l hZF hω hA hY hs hωY (η L F B U D v) (.bound 13) (.bound 6) (.bound 11)
      (.bound 10) (.bound 9) .newest rfl hZ hδ hωδ hτδ hb hc hp hm hn tuple point agree
  have quality (L F B U D v : (N₀).Domain) (hk : M.mem κ.val L.val) :
      Formula.satisfies (η L F B U D v) (et_quality_m (.bound 13) (.bound 12) (.bound 5) (.bound 8)
        (.bound 4) (.bound 7) (.bound 1) .newest) ↔
      It_local_d ω Z.val κ.val L.val F.val ∧ Sc_inaccessible_d ω Z.val L.val ∧
        Ex_strength_d hZF ω κ.val L.val Z.val F.val ∧ Et_stretch_d hZF ω κ.val L.val F.val Z.val R t.val D.val v.val :=
    et_quality_source_l hZFC trans _ (η L F B U D v) (.bound 13) (.bound 12) (.bound 5) (.bound 8)
      (.bound 4) (.bound 7) (.bound 1) .newest source hZ hδ hk hn hB₀ constants₀ pool₀ sub
  dsimp only [η, ρ] at const pools types quality
  dsimp only [UnarySchema.denote]
  simp only [ee_step_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    v_sat_l J (rt_model_ext_l hZF.1 trans _)]
  constructor
  · rintro ⟨L, hl, F, _, B, _, U, hu, D, _, v, _, hk, ht, hb, hc, hp, hv, he⟩
    have rank := (rt_fp_v_l I hZF hω hY hωY τ B).mp hb
    have constants := (const L F B U D v).mp hc
    have pool := (pools L F B U D v hu).mp hp
    exact ⟨L.val, F.val, B.val, U.val, D.val, v.val, hl, hk, ht, rank, constants, pool,
      (types L F B U D v rank constants pool).mp hv, (quality L F B U D v hk).mp he⟩
  · rintro ⟨L, F, B, U, D, v, hl, hk, ht, hb, hc, hp, hv, loc, inacc, strength, stretch⟩
    have hf : M.mem F Z.val := by obtain ⟨_, _, _, hf, _⟩ := loc; exact hf
    have hB := ZF.v_mem_l I hZF hb hZ hτδ
    have hU := tt_constants_rank_l hZF hZ hδ hτδ hb hc
    have hD := hp.rank_mem_l hZF hω hZ hδ (ZF.v_ordinal_mem_l I hZF hZ hωδ) hn hU
    have hV := ZF.v_subset_mem_l I hZF hZ hD (fun p pp => ((hv p).mp pp).1)
    let l : (N₀).Domain := ⟨L, trans δ.val δ.property L hl⟩
    let f : (N₀).Domain := ⟨F, trans Z.val Z.property F hf⟩
    let b : (N₀).Domain := ⟨B, trans Z.val Z.property B hB⟩
    let u : (N₀).Domain := ⟨U, trans Z.val Z.property U hU⟩
    let d : (N₀).Domain := ⟨D, trans Z.val Z.property D hD⟩
    let q : (N₀).Domain := ⟨v, trans Z.val Z.property v hV⟩
    exact ⟨l, hl, f, hf, b, hB, u, hU, d, hD, q, hV, hk, ht,
      (rt_fp_v_l I hZF hω hY hωY τ b).mpr hb, (const l f b u d q).mpr hc,
      (pools l f b u d q hU).mpr hp, (types l f b u d q hb hc hp).mpr hv,
      (quality l f b u d q hk).mpr ⟨loc, inacc, strength, stretch⟩⟩

include hω hA hY hs in
theorem ee_step_source_l {d} (ρ : Env N₀ d) (w κ δ n h Z t τ : Term d) (hw : w.eval ρ = ⟨ω, hωY⟩)
    {K R B U Q c S s : M.Domain} (source : Ep_source_d hZF ω (κ.eval ρ).val K (Z.eval ρ).val R)
    (hZ : V_d I (δ.eval ρ).val (Z.eval ρ).val) (hδ : M.IsLimitOrdinal (δ.eval ρ).val)
    (hωδ : M.mem ω (δ.eval ρ).val) (hτδ : M.mem (τ.eval ρ).val (δ.eval ρ).val)
    (hB : V_d I (κ.eval ρ).val B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = (κ.eval ρ).val)
    (pool : Tt_pool_d I ω (n.eval ρ).val U Q) (sub : M.MemberSubset (t.eval ρ).val Q)
    (hm : Smem_d I c A S) (hn : M.mem (n.eval ρ).val ω) (tuple : Fn0_d (n.eval ρ).val A s)
    (point : M.mem (δ.eval ρ).val A) (agree : Sx_graph_d I K₀ s (h.eval ρ).val) :
    Formula.satisfies ρ (ee_step_m w κ δ n h Z t τ) ↔
      Ee_step_d hZF ω (κ.eval ρ).val (δ.eval ρ).val (n.eval ρ).val s c (Z.eval ρ).val R (t.eval ρ).val (τ.eval ρ).val := by
  have read := ee_step_values_l hZFC hω hA hY hs hωY (κ.eval ρ) (δ.eval ρ) (n.eval ρ) (h.eval ρ)
    (Z.eval ρ) (t.eval ρ) (τ.eval ρ) source hZ hδ hωδ hτδ hB constants pool sub hm hn tuple point agree
  have env : (Definitional.Env.substitute ρ (Fin.cases τ (Fin.cases t (Fin.cases Z (Fin.cases h
      (Fin.cases n (Fin.cases δ (Fin.cases κ (fun _ => w))))))))).bound =
      ((⟨Fin.cases (t.eval ρ) (Fin.cases (Z.eval ρ) (Fin.cases (h.eval ρ) (Fin.cases (n.eval ρ)
        (Fin.cases (δ.eval ρ) (Fin.cases (κ.eval ρ) (fun _ => ⟨ω, hωY⟩)))))), fun _ => h.eval ρ⟩ : Env N₀ 7).push (τ.eval ρ)).bound := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun _ => hw))))))) i
  exact (Formula.satisfies_bind _ _ _).trans ((Formula.closed_env_l ee_step_s.body ee_step_s.freeClosed env).trans read)

end YesMetaZFC.SetTheory.LargeCardinal
