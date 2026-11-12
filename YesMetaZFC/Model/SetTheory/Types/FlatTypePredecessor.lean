import YesMetaZFC.Model.SetTheory.Types.CanonicalSource
import YesMetaZFC.Model.SetTheory.Reflection.RankSkolem
import YesMetaZFC.Model.SetTheory.Source.ClosureSyntax
import YesMetaZFC.Model.SetTheory.Internal.TupleCode
import YesMetaZFC.Model.SetTheory.Internal.LowerSatisfaction
import YesMetaZFC.Model.SetTheory.Types.CanonicalSatisfaction
import YesMetaZFC.Model.SetTheory.Types.MoveQuote
import YesMetaZFC.Model.SetTheory.Types.Embedding
import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence

/-! # 在实际极限秩层内运行原规范解码器

将解码器的全部量词限制到指定秩层，得到一条有界公式。
程序码和自然数码的秩界由已有代码全集自动供应。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def sc_num_local_m {d} (Z ω a z : Term d) : Formula 1 d := .conj (.mem a Z) (.conj (.mem z Z)
  (lr_rel_m (sc_num_m (𝒞 := kpair_convention_l) (.bound 2) (.bound 1) (.newest : Term 3)) Z
    (Fin.cases z (Fin.cases a (fun _ => ω)))))

@[simp] theorem sc_num_local_closed_l {d} (Z ω a z : Term d)
    (hZ : Z.freeSupport = []) (hω : ω.freeSupport = []) (ha : a.freeSupport = []) (hz : z.freeSupport = []) :
    (sc_num_local_m Z ω a z).FreeClosed := by
  simp only [sc_num_local_m, Definitional.Formula.FreeClosed]
  exact ⟨⟨ha, hZ⟩, ⟨⟨hz, hZ⟩, lr_rel_closed_l _ (sc_num_m_freeClosed _ _ _ rfl rfl rfl) Z _ hZ
    (Fin.cases hz (Fin.cases ha (fun _ => hω)))⟩⟩

theorem sc_num_local_delta_l {d} (Z ω a z : Term d) : (sc_num_local_m Z ω a z).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (lr_rel_delta_l ..))

/-- 对任意候选码均成立，包括无效码；没有额外解码表或源理论前提。 -/
theorem sc_num_local_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (Z ω a z : Term d)
    {δ} (hδ : M.IsLimitOrdinal δ) (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ (Z.eval ρ))
    (hω : M.IsOmega (ω.eval ρ)) (hωZ : M.mem (ω.eval ρ) (Z.eval ρ)) :
    Formula.satisfies ρ (sc_num_local_m Z ω a z) ↔
      Sc_num_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval ρ) (a.eval ρ) (z.eval ρ) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have trans := v_transitive_l I hV
  let nz : Nonempty {x // M.mem x (Z.eval ρ)} := ⟨⟨ω.eval ρ, hωZ⟩⟩
  let N := rt_model_l (Z.eval ρ) nz
  let J := rt_pair_l trans nz hZF.1 (sc_v_pair_l (ZF.modelsKP hZF) hδ hV)
  let φ := sc_num_m (𝒞 := kpair_convention_l) (.bound 2) (.bound 1) (.newest : Term 3)
  have read (ha : M.mem (a.eval ρ) (Z.eval ρ)) (hz : M.mem (z.eval ρ) (Z.eval ρ)) :
      Formula.satisfies ρ (lr_rel_m φ Z (Fin.cases z (Fin.cases a (fun _ => ω)))) ↔
        Sc_num_d I (ω.eval ρ) (a.eval ρ) (z.eval ρ) := by
    let w : N.Domain := ⟨ω.eval ρ, hωZ⟩
    let b : N.Domain := ⟨a.eval ρ, ha⟩
    let v : N.Domain := ⟨z.eval ρ, hz⟩
    let η : Env N 3 := ⟨Fin.cases v (Fin.cases b (fun _ => w)), fun _ => w⟩
    exact (sc_relative_sat_l trans nz φ (sc_num_m_freeClosed _ _ _ rfl rfl rfl)
      η ρ Z _ rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))).trans
        ((sc_num_sat_l J (rt_model_ext_l hZF.1 trans nz) η (.bound 2) (.bound 1) .newest).trans
          (rt_sc_num_l hZF hδ hV nz w b v hω))
  simp only [sc_num_local_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff]
  constructor
  · exact fun ⟨ha, hz, h⟩ => (read ha hz).mp h
  · intro h
    obtain ⟨C, code⟩ := scode_exists_l I hZF hω
    have data := h
    obtain ⟨n, F, k, _, _, hf, _⟩ := data
    have ha := trans C (scode_rank_mem_l hZF hω hδ hV hωZ code) (a.eval ρ)
      ((code (a.eval ρ)).mpr ⟨n, F, k, hf⟩)
    have hz := trans (ω.eval ρ) hωZ (z.eval ρ) (sc_num_natural_l I hZF hω h)
    exact ⟨ha, hz, (read ha hz).mpr h⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 从原自然数码恢复平坦程序的有界公式

自然数编号仍采用原 Kuratowski 规范编码。平坦程序只作为解码所得程序的
等义表示；转换证书的所有见证都留在实际的极限秩层中。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Sc_flat_d (I : kpair_convention_l.Interpretation M) (K : FlatPairing.convention.Interpretation M)
    (ω z G n r : M.Domain) : Prop := ∃ a F,
  Sc_num_d I ω a z ∧ Sformula_d I ω a n F r ∧ Sx_program_d I K F G

def sc_flat_m {d} (ω z G n r : Term d) : Formula 1 d := set[d] ⟪∃ a F,
  ⌜sc_num_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, a, ⌜z⌝ₛ) ∧
  ⌜sformula_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, a, ⌜n⌝ₛ, F, ⌜r⌝ₛ) ∧
  ⌜sx_program_m (𝒞 := kpair_convention_l) (𝒟 := FlatPairing.convention)⌝ₚ(F, ⌜G⌝ₛ)⟫
derive_free_closed sc_flat_m

theorem sc_flat_sat_l (I : kpair_convention_l.Interpretation M) (K : FlatPairing.convention.Interpretation M)
    (hE : Extensional M) {d} (ρ : Env M d) (ω z G n r : Term d) :
    Formula.satisfies ρ (sc_flat_m ω z G n r) ↔
      Sc_flat_d I K (ω.eval ρ) (z.eval ρ) (G.eval ρ) (n.eval ρ) (r.eval ρ) := by
  simp only [sc_flat_m, Sc_flat_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    sc_num_sat_l I hE, sformula_sat_l I hE, sx_program_sat_l I K hE, Definitional.Term.eval_weaken]; rfl

def sc_flat_local_m {d} (Z ω z G n r : Term d) : Formula 1 d :=
  lr_rel_m (sc_flat_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.newest : Term 5)) Z
    (Fin.cases r (Fin.cases n (Fin.cases G (Fin.cases z (fun _ => ω)))))

@[simp] theorem sc_flat_local_closed_l {d} (Z ω z G n r : Term d)
    (hZ : Z.freeSupport = []) (hω : ω.freeSupport = []) (hz : z.freeSupport = [])
    (hG : G.freeSupport = []) (hn : n.freeSupport = []) (hr : r.freeSupport = []) :
    (sc_flat_local_m Z ω z G n r).FreeClosed :=
  lr_rel_closed_l _ (sc_flat_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl) Z _ hZ
    (Fin.cases hr (Fin.cases hn (Fin.cases hG (Fin.cases hz (fun _ => hω)))))

theorem sc_flat_local_delta_l {d} (Z ω z G n r : Term d) : (sc_flat_local_m Z ω z G n r).IsDelta0 :=
  lr_rel_delta_l ..

variable (hZF : M.Models ZF) {ω δ Z : M.Domain} (hω : M.IsOmega ω)
  (hδ : M.IsLimitOrdinal δ) (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ Z) (hωZ : M.mem ω Z)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "T" => v_transitive_l I hV
local notation "nz" => Nonempty.intro (Subtype.mk ω hωZ)
local notation "N" => rt_model_l Z nz
local notation "J" => rt_pair_l T nz (And.left hZF) (sc_v_pair_l (ZF.modelsKP hZF) hδ hV)
local notation "L" => fp_rank_interpretation_l I hZF hω hV hωZ

theorem rt_sc_flat_l (z G n r : (N).Domain) :
    Sc_flat_d J L ⟨ω, hωZ⟩ z G n r ↔ Sc_flat_d I K ω z.val G.val n.val r.val := by
  have num := rt_sc_num_l hZF hδ hV nz
  have syn := rt_sformula_l (ZF.modelsKP hZF) T nz (sc_v_pair_l (ZF.modelsKP hZF) hδ hV)
  constructor
  · rintro ⟨a, F, ha, hf, code⟩
    exact ⟨a.val, F.val, (num _ a z hω).mp ha, (syn _ a n F r).mp hf,
      (rt_sx_program_l hZF hω hV hωZ hδ F G).mp code⟩
  · rintro ⟨a, F, ha, hf, code⟩
    obtain ⟨C, hc⟩ := scode_exists_l I hZF hω
    have hC := scode_rank_mem_l hZF hω hδ hV hωZ hc
    have hA := T C hC a ((hc a).mpr ⟨n.val, F, r.val, hf⟩)
    let a' : (N).Domain := ⟨a, hA⟩
    let F' : (N).Domain := ⟨F, (hf.1.mem_l M T hA).1⟩
    exact ⟨a', F', (num _ a' z hω).mpr ha, (syn _ a' n F' r).mpr hf,
      (rt_sx_program_l hZF hω hV hωZ hδ F' G).mpr code⟩

include hω hδ hV hωZ in
theorem sc_flat_local_sat_l {d} (ρ : Env M d) (U w z G n r : Term d)
    (hU : U.eval ρ = Z) (hw : w.eval ρ = ω) (hz : M.mem (z.eval ρ) Z)
    (hG : M.mem (G.eval ρ) Z) (hn : M.mem (n.eval ρ) Z) (hr : M.mem (r.eval ρ) Z) :
    Formula.satisfies ρ (sc_flat_local_m U w z G n r) ↔
      Sc_flat_d I K ω (z.eval ρ) (G.eval ρ) (n.eval ρ) (r.eval ρ) := by
  let η : Env N 5 := ⟨Fin.cases ⟨r.eval ρ, hr⟩ (Fin.cases ⟨n.eval ρ, hn⟩
    (Fin.cases ⟨G.eval ρ, hG⟩ (Fin.cases ⟨z.eval ρ, hz⟩ (fun _ => ⟨ω, hωZ⟩)))), fun _ => ⟨ω, hωZ⟩⟩
  let φ := sc_flat_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.newest : Term 5)
  exact (sc_relative_sat_l T nz φ (sc_flat_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl)
    η ρ U _ hU (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => hw)))))).trans
    ((sc_flat_sat_l J L (rt_model_ext_l hZF.1 T nz) η (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest).trans
      (rt_sc_flat_l hZF hω hδ hV hωZ ..))

end YesMetaZFC.SetTheory.Internal

/-! ## 任意较低秩层中的原自然数公式码

规范解码留在给定的极限秩层 C，真值求值仅在较低层 A 的幂集内进行。
两个层分别指定，故查询码不必属于 A，而 A 也不必是外层的前驱。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def sc_lower_s : UnarySchema 4 where
  body := .conj (.mem (.bound 1) (.bound 4)) (set[5] ⟪
    ∃ G ∈ ⌜(.bound 3 : Term 5)⌝ₛ, ∃ n ∈ ⌜(.bound 3 : Term 5)⌝ₛ, ∃ r ∈ ⌜(.bound 3 : Term 5)⌝ₛ,
      ⌜sc_flat_local_m⌝ₚ(⌜(.bound 3 : Term 5)⌝ₛ, ⌜(.bound 4 : Term 5)⌝ₛ, ⌜(.bound 1 : Term 5)⌝ₛ, G, n, r) ∧
      ⌜ft_lower_m⌝ₚ(⌜(.bound 2 : Term 5)⌝ₛ, ⌜(.bound 4 : Term 5)⌝ₛ, G, n, r, ⌜(.newest : Term 5)⌝ₛ)⟫)

def sc_lower_m {d} (ω C A z f : Term d) : Formula 1 d :=
  pred_m sc_lower_s (Fin.cases z (Fin.cases A (Fin.cases C (fun _ => ω)))) f

@[simp] theorem sc_lower_closed_l {d} (ω C A z f : Term d)
    (hw : ω.freeSupport = []) (hc : C.freeSupport = []) (ha : A.freeSupport = [])
    (hz : z.freeSupport = []) (hf : f.freeSupport = []) : (sc_lower_m ω C A z f).FreeClosed :=
  pred_m_freeClosed sc_lower_s _ _ (Fin.cases hz (Fin.cases ha (Fin.cases hc (fun _ => hw)))) hf

variable (hZF : M.Models ZF) {ω η Y : M.Domain} (hω : M.IsOmega ω)
  (hY : V_d (kp_pair_l (ZF.modelsKP hZF)) η Y) (hωY : M.mem ω Y)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "ny" => Nonempty.intro (Subtype.mk ω hωY)
local notation "N" => rt_model_l Y ny

include hω hY in
private theorem sc_lower_values_l (C A z g : (N).Domain) {ξ ν c R f : M.Domain}
    (hC : V_d Q ξ C.val) (hξ : M.IsLimitOrdinal ξ) (hωξ : M.mem ω ξ)
    (hA : V_d Q ν A.val) (hων : M.MemberSubset ω ν) (hz : M.mem z.val ω)
    (hm : Smem_d Q c A.val R) (hf : M.IsSetFunctionFromTo Q f ω A.val)
    (hg : M.IsSetFunctionFromTo K g.val ω A.val) (agree : Sx_graph_d Q K f g.val) :
    Formula.satisfies (⟨Fin.cases g (Fin.cases z (Fin.cases A (Fin.cases C (fun _ => ⟨ω, hωY⟩)))),
      fun _ => g⟩ : Env N 5) sc_lower_s.body ↔ Sc_sat_d Q ω c z.val f := by
  let ρ : Env N 5 := ⟨Fin.cases g (Fin.cases z (Fin.cases A (Fin.cases C (fun _ => ⟨ω, hωY⟩)))), fun _ => g⟩
  have ht := v_transitive_l Q hY
  have ct := v_transitive_l Q hC
  have hwC := ZF.v_ordinal_mem_l Q hZF hC hωξ
  obtain ⟨e, _, heω⟩ := hω.1.1
  obtain ⟨b, S, model⟩ := smdl_membership_l K hZF ⟨e, ZF.v_ordinal_mem_l Q hZF hA (hων e heω)⟩
  have decode (G n r : (N).Domain) (hG : M.mem G.val C.val) (hn : M.mem n.val C.val) (hr : M.mem r.val C.val) :
      Formula.satisfies (((ρ.push G).push n).push r) (sc_flat_local_m (.bound 6) (.bound 7) (.bound 4) (.bound 2) (.bound 1) .newest) ↔
        Sc_flat_d Q K ω z.val G.val n.val r.val :=
    (rt_model_delta_l ht ny (sc_flat_local_delta_l ..) _).trans
      (sc_flat_local_sat_l hZF hω hξ hC hwC _ _ _ _ _ _ _ rfl rfl (ct ω hwC z.val hz) hG hn hr)
  have read (G n r : (N).Domain) {a : M.Domain} (form : Sformula_d K ω a n.val G.val r.val) :=
    ft_lower_source_l hZF hY ny (((ρ.push G).push n).push r)
      (.bound 5) (.bound 7) (.bound 2) (.bound 1) .newest (.bound 3) hω hA hων model form hg
  simp only [sc_lower_s, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff]
  constructor
  · rintro ⟨_, G, hG, n, hn, r, hr, code, truth⟩
    obtain ⟨a, F, num, form, recode⟩ := (decode G n r hG hn hr).mp code
    obtain ⟨v, hv⟩ := (K).total G.val r.val
    have flat : Sformula_d K ω v n.val G.val r.val := ⟨hv, recode.program_l Q K form.2.1, form.2.2⟩
    exact ⟨a, num, (recode.satisfies_l Q K hZF hm model form hv hf hg agree).mpr ((read G n r flat).mp truth)⟩
  · rintro ⟨a, num, truth⟩
    have data := num
    obtain ⟨n, F, r, _, _, form, _⟩ := data
    obtain ⟨G, recode⟩ := sx_program_exists_l Q K hZF hω form.2.1
    have hn := ct ω hwC n form.2.1.1
    have hr := ct n hn r form.2.2
    have hG := fp_program_mem_l Q hZF hω hC hwC (recode.program_l Q K form.2.1)
    let G' : (N).Domain := ⟨G, ht C.val C.property G hG⟩
    let n' : (N).Domain := ⟨n, ht C.val C.property n hn⟩
    let r' : (N).Domain := ⟨r, ht C.val C.property r hr⟩
    obtain ⟨v, hv⟩ := (K).total G r
    have flat : Sformula_d K ω v n G r := ⟨hv, recode.program_l Q K form.2.1, form.2.2⟩
    exact ⟨hz, G', hG, n', hn, r', hr, (decode G' n' r' hG hn hr).mpr ⟨a, F, num, form, recode⟩,
      (read G' n' r' flat).mpr ((recode.satisfies_l Q K hZF hm model form hv hf hg agree).mp truth)⟩

include hω hY in
theorem sc_lower_source_l {d} (ρ : Env N d) (w C A z g : Term d) (hw : w.eval ρ = ⟨ω, hωY⟩)
    {ξ ν c R f : M.Domain} (hC : V_d Q ξ (C.eval ρ).val) (hξ : M.IsLimitOrdinal ξ) (hωξ : M.mem ω ξ)
    (hA : V_d Q ν (A.eval ρ).val) (hων : M.MemberSubset ω ν) (hz : M.mem (z.eval ρ).val ω)
    (hm : Smem_d Q c (A.eval ρ).val R) (hf : M.IsSetFunctionFromTo Q f ω (A.eval ρ).val)
    (hg : M.IsSetFunctionFromTo K (g.eval ρ).val ω (A.eval ρ).val) (agree : Sx_graph_d Q K f (g.eval ρ).val) :
    Formula.satisfies ρ (sc_lower_m w C A z g) ↔ Sc_sat_d Q ω c (z.eval ρ).val f := by
  have env : (Definitional.Env.substitute ρ (Fin.cases g (Fin.cases z (Fin.cases A (Fin.cases C (fun _ => w)))))).bound =
      (⟨Fin.cases (g.eval ρ) (Fin.cases (z.eval ρ) (Fin.cases (A.eval ρ)
        (Fin.cases (C.eval ρ) (fun _ => ⟨ω, hωY⟩)))), fun _ => g.eval ρ⟩ : Env N 5).bound := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => hw)))) i
  exact (Formula.satisfies_bind _ _ _).trans ((Formula.closed_env_l sc_lower_s.body sc_lower_s.freeClosed env).trans
    (sc_lower_values_l hZF hω hY hωY (C.eval ρ) (A.eval ρ) (z.eval ρ) (g.eval ρ) hC hξ hωξ hA hων hz hm hf hg agree))

end YesMetaZFC.SetTheory.Internal

/-! ## 任意外层中读取较低秩层的原完整类型查询

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
local notation "T" => v_transitive_l Q hW
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
  have trans := v_transitive_l Q hZ
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
    have eb := (tf_dom_unique_l hZF.1 (hω.transitive (ZF.modelsKP hZF)) trans he₀ hb hb₀ dom).mp hd'
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
    have hG := v_subset_mem_l Q hW A.property (fp_function_rank_l Q hZF hω hV hων nat hg)
    let z : (N).Domain := ⟨z₀, T ω hωY z₀ hz₀⟩
    let b : (N).Domain := ⟨b₀, T ω hωY b₀ hb₀⟩
    let e : (N).Domain := ⟨e₀, T B.val B.property e₀ he₀⟩
    let g' : (N).Domain := ⟨g, hG⟩
    exact ⟨z, hz₀, b, hb₀, e, he₀, (cp z b e).mpr code,
      (domain z b e).mpr ((tf_dom_unique_l hZF.1 (hω.transitive (ZF.modelsKP hZF)) trans he₀ hb₀ hb₀ dom).mpr rfl), g',
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

/-! ## 由当前最大序数自动读取完整前驱类型

原公式自行找到前一层与规范解码层。候选类型以原查询域为界，
所有查询均使用同一个平坦实现元组，包括全部内部非标准公式码。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def tf_prev_s : UnarySchema 4 where
  body := set[5] ⟪∃ ν X Z, ⌜sv_max_m⌝ₚ(ν) ∧ ⌜v_m FlatPairing.convention⌝ₚ(ν, X) ∧
    ⌜v_m FlatPairing.convention⌝ₚ(⌜(.bound 3 : Term 5)⌝ₛ, Z) ∧
    ⌜tf_query_m⌝ₚ(⌜(.bound 4 : Term 5)⌝ₛ, X, Z, ⌜(.bound 2 : Term 5)⌝ₛ,
      ⌜(.bound 1 : Term 5)⌝ₛ, ⌜(.bound 3 : Term 5)⌝ₛ, ⌜(.newest : Term 5)⌝ₛ)⟫

def tf_prev_m {d} (ω δ n h p : Term d) : Formula 1 d :=
  pred_m tf_prev_s (Fin.cases h (Fin.cases n (Fin.cases δ (fun _ => ω)))) p

@[simp] theorem tf_prev_closed_l {d} (ω δ n h p : Term d)
    (hω : ω.freeSupport = []) (hδ : δ.freeSupport = []) (hn : n.freeSupport = [])
    (hh : h.freeSupport = []) (hp : p.freeSupport = []) : (tf_prev_m ω δ n h p).FreeClosed :=
  pred_m_freeClosed tf_prev_s _ _ (Fin.cases hh (Fin.cases hn (Fin.cases hδ (fun _ => hω)))) hp

variable (hZF : M.Models ZF) {ω ν μ X Y : M.Domain} (hω : M.IsOmega ω)
  (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) ν X) (hW : V_d (kp_pair_l (ZF.modelsKP hZF)) μ Y)
  (hs : M.SuccessorOf μ ν) (hωY : M.mem ω Y)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "T" => v_transitive_l Q hW
local notation "nz" => Nonempty.intro (Subtype.mk ω hωY)
local notation "N" => rt_model_l Y nz
local notation "J" => fp_rank_interpretation_l Q hZF hω hW hωY

include hω hV hW hs in
private theorem tf_prev_values_l (n h δ p : (N).Domain) {Z c R s U D : M.Domain}
    (hZ : V_d Q δ.val Z) (hδ : M.IsLimitOrdinal δ.val) (hωδ : M.mem ω δ.val)
    (hm : Smem_d Q c X R) (hn : M.mem n.val ω) (tuple : Fn0_d n.val X s)
    (point : M.mem δ.val X) (constants : M.MemberSubset U X)
    (pool : Tt_pool_d Q ω n.val U D) (hp : M.mem p.val D) (hpZ : M.mem p.val Z)
    (agree : Sx_graph_d Q K s h.val) :
    tf_prev_s.denote (⟨Fin.cases h (Fin.cases n (Fin.cases δ (fun _ => ⟨ω, hωY⟩))), fun _ => h⟩ : Env N 4) p ↔
      Tt_query_d Q ω c n.val s δ.val p.val := by
  let ρ : Env N 5 := (⟨Fin.cases h (Fin.cases n (Fin.cases δ (fun _ => ⟨ω, hωY⟩))), fun _ => h⟩ : Env N 4).push p
  have hδν := ZF.v_ordinal_height_l hZF hV hδ.1 point
  have hων : M.MemberSubset ω ν := fun i hi =>
    (v_ordinal_l Q hV).transitive δ.val hδν i (hδ.1.transitive ω hωδ i hi)
  dsimp only [UnarySchema.denote]
  simp only [tf_prev_s, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, sv_max_sat_l,
    v_sat_l J (rt_model_ext_l hZF.1 T nz)]
  constructor
  · rintro ⟨η, A, B, greatest, layer, decode, truth⟩
    have eqη := (sv_max_rank_l Q hZF hV hW hs hωY η).mp greatest
    have layer' := (rt_fp_v_l Q hZF hω hW hωY η A).mp layer
    have eqA := ZF.v_unique_l Q hZF (eqη ▸ layer') hV
    have decode' := (rt_fp_v_l Q hZF hω hW hωY δ B).mp decode
    have eqB := ZF.v_unique_l Q hZF decode' hZ
    exact (tf_query_source_l hZF hω hW hωY (((ρ.push η).push A).push B)
      (.bound 7) (.bound 1) .newest (.bound 5) (.bound 4) (.bound 6) (.bound 3) rfl
      (eqA.symm ▸ hV) hων decode' hδ hωδ (eqA.symm ▸ hm) hn (eqA.symm ▸ tuple)
      (eqA.symm ▸ point) (eqA.symm ▸ constants) pool hp (eqB.symm ▸ hpZ) agree).mp truth
  · intro truth
    let η : (N).Domain := ⟨ν, ZF.v_ordinal_mem_l Q hZF hW hs.predecessor_mem⟩
    let A : (N).Domain := ⟨X, (ZF.v_successor_l Q hZF hV hW hs X).mpr (fun _ h => h)⟩
    let B : (N).Domain := ⟨Z, ZF.v_mem_l Q hZF hZ hW (ZF.v_ordinal_height_l hZF hW hδ.1 δ.property)⟩
    exact ⟨η, A, B, (sv_max_rank_l Q hZF hV hW hs hωY η).mpr rfl,
      (rt_fp_v_l Q hZF hω hW hωY η A).mpr hV,
      (rt_fp_v_l Q hZF hω hW hωY δ B).mpr hZ,
      (tf_query_source_l hZF hω hW hωY (((ρ.push η).push A).push B)
        (.bound 7) (.bound 1) .newest (.bound 5) (.bound 4) (.bound 6) (.bound 3) rfl
        hV hων hZ hδ hωδ hm hn tuple point constants pool hp hpZ agree).mpr truth⟩

include hω hV hW hs in
theorem tf_prev_source_l {d} (ρ : Env N d) (w δ n h p : Term d) (hw : w.eval ρ = ⟨ω, hωY⟩)
    {Z c R s U D : M.Domain} (hZ : V_d Q (δ.eval ρ).val Z)
    (hδ : M.IsLimitOrdinal (δ.eval ρ).val) (hωδ : M.mem ω (δ.eval ρ).val)
    (hm : Smem_d Q c X R) (hn : M.mem (n.eval ρ).val ω) (tuple : Fn0_d (n.eval ρ).val X s)
    (point : M.mem (δ.eval ρ).val X) (constants : M.MemberSubset U X)
    (pool : Tt_pool_d Q ω (n.eval ρ).val U D) (hp : M.mem (p.eval ρ).val D) (hpZ : M.mem (p.eval ρ).val Z)
    (agree : Sx_graph_d Q K s (h.eval ρ).val) : Formula.satisfies ρ (tf_prev_m w δ n h p) ↔
      Tt_query_d Q ω c (n.eval ρ).val s (δ.eval ρ).val (p.eval ρ).val := by
  have env : (Definitional.Env.substitute ρ (Fin.cases p (Fin.cases h (Fin.cases n (Fin.cases δ (fun _ => w)))))).bound =
      ((⟨Fin.cases (h.eval ρ) (Fin.cases (n.eval ρ) (Fin.cases (δ.eval ρ) (fun _ => ⟨ω, hωY⟩))),
        fun _ => h.eval ρ⟩ : Env N 4).push (p.eval ρ)).bound := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => hw)))) i
  exact (Formula.satisfies_bind _ _ _).trans
    ((Formula.closed_env_l tf_prev_s.body tf_prev_s.freeClosed env).trans
      (tf_prev_values_l hZF hω hV hW hs hωY (n.eval ρ) (h.eval ρ) (δ.eval ρ) (p.eval ρ)
        hZ hδ hωδ hm hn tuple point constants pool hp hpZ agree))

def tf_type_m {d} (ω δ n h D t : Term d) : Formula 1 d := set[d] ⟪
  ⌜t⌝ₛ ⊆ ⌜D⌝ₛ ∧ (∀ p ∈ ⌜D⌝ₛ, p ∈ ⌜t⌝ₛ ↔ ⌜tf_prev_m⌝ₚ(⌜ω⌝ₛ, ⌜δ⌝ₛ, ⌜n⌝ₛ, ⌜h⌝ₛ, p))⟫
derive_free_closed tf_type_m

include hω hV hW hs in
theorem tf_type_source_l {d} (ρ : Env N d) (w δ n h D t : Term d) (hw : w.eval ρ = ⟨ω, hωY⟩)
    {Z c R s U : M.Domain} (hZ : V_d Q (δ.eval ρ).val Z)
    (hδ : M.IsLimitOrdinal (δ.eval ρ).val) (hωδ : M.mem ω (δ.eval ρ).val)
    (hm : Smem_d Q c X R) (hn : M.mem (n.eval ρ).val ω) (tuple : Fn0_d (n.eval ρ).val X s)
    (point : M.mem (δ.eval ρ).val X) (constants : M.MemberSubset U X)
    (pool : Tt_pool_d Q ω (n.eval ρ).val U (D.eval ρ).val) (hD : M.mem (D.eval ρ).val Z)
    (agree : Sx_graph_d Q K s (h.eval ρ).val) : Formula.satisfies ρ (tf_type_m w δ n h D t) ↔
      Tt_truth_d Q ω c (n.eval ρ).val s (δ.eval ρ).val (D.eval ρ).val (t.eval ρ).val := by
  have read (p : (N).Domain) (hp : M.mem p.val (D.eval ρ).val) :
      Formula.satisfies (ρ.push p) (tf_prev_m w.weaken δ.weaken n.weaken h.weaken .newest) ↔
        Tt_query_d Q ω c (n.eval ρ).val s (δ.eval ρ).val p.val := by
    have q := tf_prev_source_l hZF hω hV hW hs hωY (ρ.push p) w.weaken δ.weaken n.weaken h.weaken .newest
    simp only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest] at q
    exact q hw hZ hδ hωδ hm hn tuple point constants pool hp
      (v_transitive_l Q hZ (D.eval ρ).val hD p.val hp) agree
  simp only [tf_type_m, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨sub, matrix⟩ p
    constructor
    · intro hp
      let q : (N).Domain := ⟨p, T (t.eval ρ).val (t.eval ρ).property p hp⟩
      have hpD := sub q hp
      exact ⟨hpD, (read q hpD).mp ((matrix q hpD).mp hp)⟩
    · rintro ⟨hpD, truth⟩
      let q : (N).Domain := ⟨p, T (D.eval ρ).val (D.eval ρ).property p hpD⟩
      exact (matrix q hpD).mpr ((read q hpD).mpr truth)
  · intro truth
    exact ⟨fun p hp => ((truth p.val).mp hp).1, fun p hp =>
      (truth p.val).trans ((and_iff_right hp).trans (read p hp).symm)⟩

end YesMetaZFC.SetTheory.Internal
