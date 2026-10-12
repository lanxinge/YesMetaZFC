import YesMetaZFC.Model.SetTheory.Internal.FlatTypeNames
import YesMetaZFC.Model.SetTheory.Internal.CanonicalRank
import YesMetaZFC.Model.SetTheory.Internal.TypeTruth

/-! # 任意外层中读取较低秩层的原完整类型查询

查询码和名字列保持原编码。名字列的定义域及平坦赋值由有界矩阵检验，
原 Kuratowski 元组、中间列和完整赋值仅用于背景证明，不作为源内见证。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Tf_dom_d (ω Z b e : M.Domain) : Prop := ∀ i, M.mem i ω →
  (M.mem i b ↔ ∃ a, M.mem a Z ∧ Rd_entry_d i a e)

def tf_dom0_m {d} (ω Z b e : Term d) : Formula 1 d := set[d] ⟪∀ i ∈ ⌜ω⌝ₛ,
  i ∈ ⌜b⌝ₛ ↔ (∃ a ∈ ⌜Z⌝ₛ, ⌜rd_entry0_m⌝ₚ(i, a, ⌜e⌝ₛ))⟫
derive_free_closed tf_dom0_m

theorem tf_dom0_delta_l {d} (ω Z b e : Term d) : (tf_dom0_m ω Z b e).IsDelta0 :=
  .forallMem _ (.iff (.mem _ _) (.existsMem _ (rd_entry0_delta_l ..)))

theorem tf_dom0_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω Z b e : Term d) :
    Formula.satisfies ρ (tf_dom0_m ω Z b e) ↔ Tf_dom_d (ω.eval ρ) (Z.eval ρ) (b.eval ρ) (e.eval ρ) := by
  simp only [tf_dom0_m, Tf_dom_d, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, rd_entry0_sat_l hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem tf_dom_unique_l (hE : Extensional M) {ω Z b k e : M.Domain}
    (hω : M.TransitiveSet ω) (hZ : M.TransitiveSet Z) (he : M.mem e Z) (hb : M.mem b ω) (hk : M.mem k ω)
    (dom : ∀ i, M.mem i k ↔ ∃ a, Rd_entry_d i a e) : Tf_dom_d ω Z b e ↔ b = k := by
  have read i : (∃ a, M.mem a Z ∧ Rd_entry_d i a e) ↔ M.mem i k :=
    ⟨fun ⟨a, _, ha⟩ => (dom i).mpr ⟨a, ha⟩, fun hi => by
      obtain ⟨a, ha⟩ := (dom i).mp hi
      exact ⟨a, (rd_entry_transitive_l hZ he ha).2, ha⟩⟩
  refine ⟨fun matrix => hE.eq_of_same_members b k (fun i => ⟨?_, ?_⟩), ?_⟩
  · intro hi
    exact (read i).mp ((matrix i (hω b hb i hi)).mp hi)
  · intro hi
    exact (matrix i (hω k hk i hi)).mpr ((read i).mpr hi)
  · rintro rfl i _
    exact (read i).symm

def tf_query_s : UnarySchema 6 where
  body := set[7] ⟪∃ z ∈ ⌜(.bound 6 : Term 7)⌝ₛ, ∃ b ∈ ⌜(.bound 6 : Term 7)⌝ₛ, ∃ e ∈ ⌜(.bound 4 : Term 7)⌝ₛ,
    ⌜kpair0_m⌝ₚ(⌜(.newest : Term 7)⌝ₛ, z, e) ∧
    ⌜tf_dom0_m⌝ₚ(⌜(.bound 6 : Term 7)⌝ₛ, ⌜(.bound 4 : Term 7)⌝ₛ, b, e) ∧
    (∃ g, ⌜Formula.isFunctionFromTo FlatPairing.convention⌝ₚ(g, ⌜(.bound 6 : Term 7)⌝ₛ, ⌜(.bound 5 : Term 7)⌝ₛ) ∧
      ⌜tf_fill0_m⌝ₚ(⌜(.bound 6 : Term 7)⌝ₛ, ⌜(.bound 5 : Term 7)⌝ₛ, ⌜(.bound 4 : Term 7)⌝ₛ,
        ⌜(.bound 3 : Term 7)⌝ₛ, ⌜(.bound 2 : Term 7)⌝ₛ, ⌜(.bound 1 : Term 7)⌝ₛ, b, e, g) ∧
      ⌜sc_lower_m⌝ₚ(⌜(.bound 6 : Term 7)⌝ₛ, ⌜(.bound 4 : Term 7)⌝ₛ, ⌜(.bound 5 : Term 7)⌝ₛ, z, g))⟫

def tf_query_m {d} (ω X Z n h δ p : Term d) : Formula 1 d :=
  pred_m tf_query_s (Fin.cases δ (Fin.cases h (Fin.cases n (Fin.cases Z (Fin.cases X (fun _ => ω)))))) p

@[simp] theorem tf_query_closed_l {d} (ω X Z n h δ p : Term d)
    (hω : ω.freeSupport = []) (hX : X.freeSupport = []) (hZ : Z.freeSupport = [])
    (hn : n.freeSupport = []) (hh : h.freeSupport = []) (hδ : δ.freeSupport = []) (hp : p.freeSupport = []) :
    (tf_query_m ω X Z n h δ p).FreeClosed :=
  pred_m_freeClosed tf_query_s _ _ (Fin.cases hδ (Fin.cases hh (Fin.cases hn (Fin.cases hZ (Fin.cases hX (fun _ => hω)))))) hp

variable (hZF : M.Models ZF) {ω μ Y : M.Domain} (hω : M.IsOmega ω)
  (hW : V_d (kp_pair_l (ZF.modelsKP hZF)) μ Y) (hωY : M.mem ω Y)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "T" => ZF.v_transitive_l Q hZF hW
local notation "nz" => Nonempty.intro (Subtype.mk ω hωY)
local notation "N" => rt_model_l Y nz
local notation "J" => fp_rank_interpretation_l Q hZF hω hW hωY

include hω hW in
private theorem tf_query_values_l (A B n h δ p : (N).Domain) {ν ξ : M.Domain}
    (hV : V_d Q ν A.val) (hων : M.MemberSubset ω ν)
    (hZ : V_d Q ξ B.val) (hξ : M.IsLimitOrdinal ξ) (hωξ : M.mem ω ξ)
    {c R s U D : M.Domain} (hm : Smem_d Q c A.val R) (hn : M.mem n.val ω)
    (tuple : Fn0_d n.val A.val s) (point : M.mem δ.val A.val) (constants : M.MemberSubset U A.val)
    (pool : Tt_pool_d Q ω n.val U D) (hp : M.mem p.val D) (hpZ : M.mem p.val B.val)
    (agree : Sx_graph_d Q K s h.val) :
    tf_query_s.denote (⟨Fin.cases δ (Fin.cases h (Fin.cases n (Fin.cases B
      (Fin.cases A (fun _ => ⟨ω, hωY⟩))))), fun _ => h⟩ : Env N 6) p ↔
      Tt_query_d Q ω c n.val s δ.val p.val := by
  let ρ : Env N 7 := (⟨Fin.cases δ (Fin.cases h (Fin.cases n (Fin.cases B
    (Fin.cases A (fun _ => ⟨ω, hωY⟩))))), fun _ => h⟩ : Env N 6).push p
  have trans := ZF.v_transitive_l Q hZF hZ
  obtain ⟨z₀, b₀, e₀, r₀, f₀, code, hz₀, hb₀, dom, assign, fill, fn, query⟩ :=
    pool.realize_l hZF hω (c := c) hn tuple point constants hp
  have he₀ := (code.mem_l M trans hpZ).2
  have ff := fn0_function_l (ZF.modelsKP hZF) fn
  -- 三个有界矩阵直接穿过 Y；原名字列的域随后由外延性唯一恢复。
  have cp (z b e : (N).Domain) : Formula.satisfies (((ρ.push z).push b).push e)
      (kpair0_m (.bound 3) (.bound 2) .newest) ↔ (Q).Codes p.val z.val e.val := by
    exact (rt_model_delta_l T nz (kpair0_delta_l ..) _).trans
      (kpair0_sat_l hZF.1 _ (.bound 3) (.bound 2) .newest)
  have domain (z b e : (N).Domain) : Formula.satisfies (((ρ.push z).push b).push e)
      (tf_dom0_m (.bound 9) (.bound 7) (.bound 1) .newest) ↔ Tf_dom_d ω B.val b.val e.val := by
    exact (rt_model_delta_l T nz (tf_dom0_delta_l ..) _).trans
      (tf_dom0_sat_l hZF.1 _ (.bound 9) (.bound 7) (.bound 1) .newest)
  have matrix (z b e g : (N).Domain) : Formula.satisfies ((((ρ.push z).push b).push e).push g)
      (tf_fill0_m (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 2) (.bound 1) .newest) ↔
        Tf_fill_d K ω A.val B.val n.val h.val δ.val b.val e.val g.val := by
    exact (rt_model_delta_l T nz (tf_fill0_delta_l ..) _).trans
      (tf_fill0_sat_l (ZF.models_kpi_l hZF) _ (.bound 10) (.bound 9) (.bound 8) (.bound 7)
        (.bound 6) (.bound 5) (.bound 2) (.bound 1) .newest hω)
  have prev (z b e g : (N).Domain) (hz : M.mem z.val ω) (hg : M.IsSetFunctionFromTo K g.val ω A.val)
      (fg : Sx_graph_d Q K f₀ g.val) :
      Formula.satisfies ((((ρ.push z).push b).push e).push g)
        (sc_lower_m (.bound 10) (.bound 8) (.bound 9) (.bound 3) .newest) ↔ Sc_sat_d Q ω c z.val f₀ :=
    sc_lower_source_l hZF hω hW hωY ((((ρ.push z).push b).push e).push g)
      (.bound 10) (.bound 8) (.bound 9) (.bound 3) .newest rfl hZ hξ hωξ hV hων hz hm ff hg fg
  dsimp only [UnarySchema.denote]
  simp only [tf_query_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_isFunctionFromTo_iff J (rt_model_ext_l hZF.1 T nz),
    Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨z, hz, b, hb, e, he, pair, hd, g, hg, mat, truth⟩
    obtain ⟨ez, ee⟩ := (Q).injective ((cp z b e).mp pair) code
    have hd' := (domain z b e).mp hd
    rw [ee] at hd'
    have eb := (tf_dom_unique_l hZF.1 (hω.transitive hZF) trans he₀ hb hb₀ dom).mp hd'
    have hg' := (rt_fp_function_from_l Q hZF hω hW hωY g ⟨ω, hωY⟩ A).mp hg
    have mat' := (matrix z b e g).mp mat
    rw [ee, eb] at mat'
    have fg := (tf_fill_iff_l hZF trans he₀ agree assign fill ff hg').mp mat'
    have result := (prev z b e g hz hg' fg).mp truth
    exact query.mpr (ez ▸ result)
  · intro truth
    -- 只把重编码后的完整赋值送入 Y；原 r₀、f₀ 仍留在背景中。
    obtain ⟨g, hg, fg⟩ := fn_recode_l Q K hZF ff
    have nat : M.MemberSubset ω A.val := fun i hi => ZF.v_ordinal_mem_l Q hZF hV (hων i hi)
    have hG := ZF.v_subset_mem_l Q hZF hW A.property (fp_function_rank_l Q hZF hω hV hων nat hg)
    let z : (N).Domain := ⟨z₀, T ω hωY z₀ hz₀⟩
    let b : (N).Domain := ⟨b₀, T ω hωY b₀ hb₀⟩
    let e : (N).Domain := ⟨e₀, T B.val B.property e₀ he₀⟩
    let g' : (N).Domain := ⟨g, hG⟩
    exact ⟨z, hz₀, b, hb₀, e, he₀, (cp z b e).mpr code,
      (domain z b e).mpr ((tf_dom_unique_l hZF.1 (hω.transitive hZF) trans he₀ hb₀ hb₀ dom).mpr rfl), g',
      (rt_fp_function_from_l Q hZF hω hW hωY g' ⟨ω, hωY⟩ A).mpr hg,
      (matrix z b e g').mpr ((tf_fill_iff_l hZF trans he₀ agree assign fill ff hg).mpr fg),
      (prev z b e g' hz₀ hg fg).mpr (query.mp truth)⟩

include hω hW in
theorem tf_query_source_l {d} (ρ : Env N d) (w A B n h δ p : Term d) (hw : w.eval ρ = ⟨ω, hωY⟩)
    {ν ξ : M.Domain} (hV : V_d Q ν (A.eval ρ).val) (hων : M.MemberSubset ω ν)
    (hZ : V_d Q ξ (B.eval ρ).val) (hξ : M.IsLimitOrdinal ξ) (hωξ : M.mem ω ξ)
    {c R s U D : M.Domain} (hm : Smem_d Q c (A.eval ρ).val R) (hn : M.mem (n.eval ρ).val ω)
    (tuple : Fn0_d (n.eval ρ).val (A.eval ρ).val s) (point : M.mem (δ.eval ρ).val (A.eval ρ).val)
    (constants : M.MemberSubset U (A.eval ρ).val) (pool : Tt_pool_d Q ω (n.eval ρ).val U D)
    (hp : M.mem (p.eval ρ).val D) (hpZ : M.mem (p.eval ρ).val (B.eval ρ).val)
    (agree : Sx_graph_d Q K s (h.eval ρ).val) : Formula.satisfies ρ (tf_query_m w A B n h δ p) ↔
      Tt_query_d Q ω c (n.eval ρ).val s (δ.eval ρ).val (p.eval ρ).val := by
  have env : (Definitional.Env.substitute ρ (Fin.cases p (Fin.cases δ (Fin.cases h (Fin.cases n
      (Fin.cases B (Fin.cases A (fun _ => w)))))))).bound =
      ((⟨Fin.cases (δ.eval ρ) (Fin.cases (h.eval ρ) (Fin.cases (n.eval ρ) (Fin.cases (B.eval ρ)
        (Fin.cases (A.eval ρ) (fun _ => ⟨ω, hωY⟩))))), fun _ => h.eval ρ⟩ : Env N 6).push (p.eval ρ)).bound := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun _ => hw)))))) i
  exact (Formula.satisfies_bind _ _ _).trans
    ((Formula.closed_env_l tf_query_s.body tf_query_s.freeClosed env).trans
      (tf_query_values_l hZF hω hW hωY (A.eval ρ) (B.eval ρ) (n.eval ρ) (h.eval ρ) (δ.eval ρ) (p.eval ρ)
        hV hων hZ hξ hωξ hm hn tuple point constants pool hp hpZ agree))

end YesMetaZFC.SetTheory.Internal
