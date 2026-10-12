import YesMetaZFC.SetTheory.LargeCardinal.TypeElasticStep

/-! # 同一元组的全高度弹性公式

原公式先读取元组在前一层的完整 κ 型，再对全部 τ<δ 量化实际扩展器。
源、原 κ 型及每次伸展的候选类型均在公式内部绑定。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ee_realized_d (hZF : M.Models ZF) (ω κ δ n s c X R : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ B U D t, V_d I κ B ∧ (∀ x, M.mem x U ↔ M.mem x B ∨ x = κ) ∧
    Tt_pool_d I ω n U D ∧ Tt_truth_d I ω c n s δ D t ∧ ∀ τ, M.mem τ δ → Ee_step_d hZF ω κ δ n s c X R t τ

def ee_realized_s : UnarySchema 4 where
  body := set[5] ⟪∃ Z, ⌜v_m FlatPairing.convention⌝ₚ(⌜(.bound 2 : Term 5)⌝ₛ, Z) ∧
    (∃ t ∈ Z, ⌜tf_kappa_m⌝ₚ(⌜(.bound 4 : Term 5)⌝ₛ, ⌜(.bound 3 : Term 5)⌝ₛ,
      ⌜(.bound 2 : Term 5)⌝ₛ, ⌜(.bound 1 : Term 5)⌝ₛ, ⌜(.newest : Term 5)⌝ₛ, t) ∧
      (∀ τ ∈ ⌜(.bound 2 : Term 5)⌝ₛ, ⌜ee_step_m⌝ₚ(⌜(.bound 4 : Term 5)⌝ₛ, ⌜(.bound 3 : Term 5)⌝ₛ,
        ⌜(.bound 2 : Term 5)⌝ₛ, ⌜(.bound 1 : Term 5)⌝ₛ, ⌜(.newest : Term 5)⌝ₛ, Z, t, τ)))⟫

def ee_realized_m {d} (ω κ δ n h : Term d) : Formula 1 d :=
  pred_m ee_realized_s (Fin.cases n (Fin.cases δ (Fin.cases κ (fun _ => ω)))) h
@[simp] theorem ee_realized_closed_l {d} (ω κ δ n h : Term d)
    (hw : ω.freeSupport = []) (hk : κ.freeSupport = []) (hd : δ.freeSupport = [])
    (hn : n.freeSupport = []) (hh : h.freeSupport = []) : (ee_realized_m ω κ δ n h).FreeClosed :=
  pred_m_freeClosed ee_realized_s _ _ (Fin.cases hn (Fin.cases hd (Fin.cases hk (fun _ => hw)))) hh

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
private theorem ee_realized_values_l (κ δ n h : (N₀).Domain) {K X R c S s : M.Domain}
    (source : Ep_source_d hZF ω κ.val K X R) (hX : V_d I δ.val X)
    (hδ : M.IsLimitOrdinal δ.val) (hωδ : M.mem ω δ.val) (hκδ : M.mem κ.val δ.val)
    (hm : Smem_d I c A S) (hn : M.mem n.val ω) (tuple : Fn0_d n.val A s) (point : M.mem δ.val A)
    (agree : Sx_graph_d I K₀ s h.val) :
    ee_realized_s.denote (⟨Fin.cases n (Fin.cases δ (Fin.cases κ (fun _ => ⟨ω, hωY⟩))),
      fun _ => h⟩ : Env N₀ 4) h ↔ Ee_realized_d hZF ω κ.val δ.val n.val s c X R := by
  let ρ := (⟨Fin.cases n (Fin.cases δ (Fin.cases κ (fun _ => ⟨ω, hωY⟩))), fun _ => h⟩ : Env N₀ 4).push h
  have trans := ZF.v_transitive_l I hZF hY
  obtain ⟨B, U, hb, hu, constants⟩ := tt_constants_exists_l hZF hX hδ hκδ
  obtain ⟨D, pool⟩ := tt_pool_exists_l I hZF hω n.val U
  have hD := pool.rank_mem_l hZF hω hX hδ source.omega_mem hn hu
  have types (Z t : (N₀).Domain) : Formula.satisfies ((ρ.push Z).push t)
      (tf_kappa_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) .newest) ↔
        Tt_truth_d I ω c n.val s δ.val D t.val :=
    tf_kappa_source_l hZF hω hA hY hs hωY ((ρ.push Z).push t) (.bound 6) (.bound 5) (.bound 4) (.bound 3)
      (.bound 2) .newest rfl hX hδ hωδ hκδ hb constants pool hm hn tuple point agree
  have all (Z t : (N₀).Domain) (eq : Z.val = X) (truth : Tt_truth_d I ω c n.val s δ.val D t.val) :
      Formula.satisfies ((ρ.push Z).push t) (Formula.forallMem (.bound 4)
        (ee_step_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)) ↔
      ∀ τ, M.mem τ δ.val → Ee_step_d hZF ω κ.val δ.val n.val s c X R t.val τ := by
    have read (τ : (N₀).Domain) (ht : M.mem τ.val δ.val) :=
      ee_step_source_l hZFC hω hA hY hs hωY (((ρ.push Z).push t).push τ) (.bound 7) (.bound 6) (.bound 5)
        (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest rfl (eq.symm ▸ source) (eq.symm ▸ hX) hδ hωδ ht
        hb constants pool (fun p pp => ((truth p).mp pp).1) hm hn tuple point agree
    simp only [Formula.satisfies_forallMem_iff]
    exact ⟨fun h τ ht => eq ▸ (read ⟨τ, trans δ.val δ.property τ ht⟩ ht).mp (h ⟨τ, trans δ.val δ.property τ ht⟩ ht),
      fun h τ ht => (read τ ht).mpr (eq.symm ▸ h τ.val ht)⟩
  dsimp only [ρ] at types all
  dsimp only [UnarySchema.denote]
  simp only [ee_realized_s, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    v_sat_l J (rt_model_ext_l hZF.1 trans _), Formula.satisfies_existsMem_iff]
  constructor
  · rintro ⟨Z, hz, t, _, truth, steps⟩
    have eq := ZF.v_unique_l I hZF ((rt_fp_v_l I hZF hω hY hωY δ Z).mp hz) hX
    have type := (types Z t).mp truth
    exact ⟨B, U, D, t.val, hb, constants, pool, type, (all Z t eq type).mp steps⟩
  · rintro ⟨B', U', D', t, hb', hc', hp', truth, steps⟩
    have eqB := ZF.v_unique_l I hZF hb' hb
    subst B'
    have eqU := hZF.1.eq_of_same_members U' U (fun x => (hc' x).trans (constants x).symm)
    subst U'
    have eqD := hp'.unique_l hZF.1 I pool
    subst D'
    have hδν := ZF.v_ordinal_height_l hZF hA hδ.1 point
    let Z : (N₀).Domain := ⟨X, ZF.v_mem_l I hZF hX hY ((hs δ.val).mpr (Or.inl hδν))⟩
    have ht := ZF.v_subset_mem_l I hZF hX hD (fun p pp => ((truth p).mp pp).1)
    let q : (N₀).Domain := ⟨t, trans X Z.property t ht⟩
    exact ⟨Z, (rt_fp_v_l I hZF hω hY hωY δ Z).mpr hX, q, ht,
      (types Z q).mpr truth, (all Z q rfl truth).mpr steps⟩

include hω hA hY hs in
theorem ee_realized_source_l {d} (ρ : Env N₀ d) (w κ δ n h : Term d) (hw : w.eval ρ = ⟨ω, hωY⟩)
    {K X R c S s : M.Domain} (source : Ep_source_d hZF ω (κ.eval ρ).val K X R)
    (hX : V_d I (δ.eval ρ).val X) (hδ : M.IsLimitOrdinal (δ.eval ρ).val)
    (hωδ : M.mem ω (δ.eval ρ).val) (hκδ : M.mem (κ.eval ρ).val (δ.eval ρ).val)
    (hm : Smem_d I c A S) (hn : M.mem (n.eval ρ).val ω) (tuple : Fn0_d (n.eval ρ).val A s)
    (point : M.mem (δ.eval ρ).val A) (agree : Sx_graph_d I K₀ s (h.eval ρ).val) :
    Formula.satisfies ρ (ee_realized_m w κ δ n h) ↔
      Ee_realized_d hZF ω (κ.eval ρ).val (δ.eval ρ).val (n.eval ρ).val s c X R := by
  have read := ee_realized_values_l hZFC hω hA hY hs hωY (κ.eval ρ) (δ.eval ρ) (n.eval ρ) (h.eval ρ)
    source hX hδ hωδ hκδ hm hn tuple point agree
  have env : (Definitional.Env.substitute ρ (Fin.cases h (Fin.cases n (Fin.cases δ (Fin.cases κ (fun _ => w)))))).bound =
      ((⟨Fin.cases (n.eval ρ) (Fin.cases (δ.eval ρ) (Fin.cases (κ.eval ρ) (fun _ => ⟨ω, hωY⟩))),
        fun _ => h.eval ρ⟩ : Env N₀ 4).push (h.eval ρ)).bound := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => hw)))) i
  exact (Formula.satisfies_bind _ _ _).trans ((Formula.closed_env_l ee_realized_s.body ee_realized_s.freeClosed env).trans read)

end YesMetaZFC.SetTheory.LargeCardinal
