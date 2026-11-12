import YesMetaZFC.SetTheory.Notation
import YesMetaZFC.SetTheory.LargeCardinal.Extender.BoundedTransport
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Trace
import YesMetaZFC.Model.SetTheory.Relations.Parity
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptMember

/-! # 所属模型中的最大强度证书

用实际的 j(P(κ)) 读取支撑以下的子集覆盖。整个有界超幂和求值图均在所属
模型中构造；强度条款只量化该模型已有的子集，因而可随完整初等图传输。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Es_strength_d (X L Y : M.Domain) : Prop :=
  (∀ α, M.mem α L → ∀ x, M.mem x X → M.MemberSubset x α → M.mem x Y) ∧
    ∃ x, M.mem x X ∧ M.MemberSubset x L ∧ ¬ M.mem x Y

def es_strength_m {d} (L Y : Term d) : Formula 1 d := .conj
  (Formula.forallMem L (.forallE (.imp (Formula.subset .newest (.bound 1)) (.mem .newest Y.weaken.weaken))))
  (.existsE (.conj (Formula.subset .newest L.weaken) (.neg (.mem .newest Y.weaken))))
derive_free_closed es_strength_m

theorem es_strength_relative_l {X : M.Domain} (hX : M.TransitiveSet X)
    (nx : Nonempty {x // M.mem x X}) {d} (ρ : Env (rt_model_l X nx) d) (L Y : Term d) :
    Formula.satisfies ρ (es_strength_m L Y) ↔ Es_strength_d X (L.eval ρ).val (Y.eval ρ).val := by
  have sub {n} (η : Env (rt_model_l X nx) n) (a b : Term n) : Formula.satisfies η (Formula.subset a b) ↔
      M.MemberSubset (a.eval η).val (b.eval η).val := by
    simpa only [Formula.subset, Structure.MemberSubset, eval_image_env_l (M := rt_model_l X nx) (N := M) Subtype.val] using
      (rt_model_delta_l hX nx (.atom ..) η).trans (Formula.satisfies_subset_iff _ a b)
  simp only [es_strength_m, Es_strength_d, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, sub, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨lower, x, hx, missing⟩
    exact ⟨fun α hα y hy hyα => lower ⟨α, hX (L.eval ρ).val (L.eval ρ).property α hα⟩ hα ⟨y, hy⟩ hyα,
      x.val, x.property, hx, missing⟩
  · rintro ⟨lower, x, hx, sub, missing⟩
    exact ⟨fun α hα y hy => lower α.val hα y.val y.property hy, ⟨x, hx⟩, sub, missing⟩

theorem es_strength_map_l (hZF : M.Models ZF) {ω c d X R Y S j L L' B B' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j)
    (hL : Rd_entry_d L L' j) (hB : Rd_entry_d B B' j) : Es_strength_d X L B ↔ Es_strength_d Y L' B' := by
  let nx : Nonempty {x // M.mem x X} := ⟨⟨L, hj.1.1.input_mem_of_pairMember hL⟩⟩
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨L', hj.1.1.output_mem_of_pairMember hL⟩⟩
  let ρ : Env (rt_model_l X nx) 2 := ⟨Fin.cases ⟨B, hj.1.1.input_mem_of_pairMember hB⟩
    (fun _ => ⟨L, hj.1.1.input_mem_of_pairMember hL⟩), fun _ => ⟨L, hj.1.1.input_mem_of_pairMember hL⟩⟩
  let η : Env (rt_model_l Y ny) 2 := ⟨Fin.cases ⟨B', hj.1.1.output_mem_of_pairMember hB⟩
    (fun _ => ⟨L', hj.1.1.output_mem_of_pairMember hL⟩), fun _ => ⟨L', hj.1.1.output_mem_of_pairMember hL⟩⟩
  obtain ⟨z, hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l _ hZF hω ⟨c, R, d, S, hm.empty_pred_l _ hz, hn.empty_pred_l _ hz, hj⟩ nx ny
    (es_strength_m (.bound 1) .newest) (by simp -implicitDefEqProofs) ρ η (Fin.cases hB (fun _ => hL))
  exact (es_strength_relative_l hX nx ρ ..).symm.trans (tr.trans (es_strength_relative_l hY ny η ..))

/-- 相对幂集、有界节点、原测度关系与实际求值图共同刻画同一张扩展器的强度。 -/
def Ex_strength_d (I : kpair_convention_l.Interpretation M) (ω κ L X F : M.Domain) : Prop :=
  M.mem ω X ∧ M.mem κ X ∧ M.mem L X ∧ M.mem F X ∧ M.IsOrdinal L ∧
    ∃ K P A Q Y e, M.mem K X ∧ M.mem P X ∧ M.mem Y X ∧
      Fseq_space_d I ω κ K ∧ FilterZF.Source_d X κ P ∧
      Eb_collapse_d ω κ L K X P F A Q Y e ∧ Es_strength_d X L Y

def es_strength0_m {d} (X L Y : Term d) : Formula 1 d := set[d] ⟪
  (∀ α ∈ ⌜L⌝ₛ, ∀ x ∈ ⌜X⌝ₛ, x ⊆ α → x ∈ ⌜Y⌝ₛ) ∧
  (∃ x ∈ ⌜X⌝ₛ, x ⊆ ⌜L⌝ₛ ∧ x ∉ ⌜Y⌝ₛ)⟫
derive_free_closed es_strength0_m

theorem es_strength0_delta_l {d} (X L Y : Term d) : (es_strength0_m X L Y).IsDelta0 :=
  .conj (.forallMem _ (.forallMem _ (.imp (.atom ..) (.mem ..))))
    (.existsMem _ (.conj (.atom ..) (.neg (.mem ..))))

theorem es_strength0_sat_l {d} (ρ : Env M d) (X L Y : Term d) :
    Formula.satisfies ρ (es_strength0_m X L Y) ↔ Es_strength_d (X.eval ρ) (L.eval ρ) (Y.eval ρ) := by
  simp only [es_strength0_m, Es_strength_d, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, Definitional.Term.eval_weaken]; rfl

/-- 传输实际有界超幂、求值图以及相对最大强度，保留目标扩展器的全部证据。 -/
theorem Ex_strength_d.map_l (hZF : M.Models ZF) {ω c d X R Y S j κ κ' L L' F F' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j)
    (theory : Sc_theory_d (kp_pair_l (ZF.modelsKP hZF)) ω Y S)
    (hκ : Rd_entry_d κ κ' j) (hL : Rd_entry_d L L' j) (hF : Rd_entry_d F F' j)
    (h : Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X F) : Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' L' Y F' := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨hωX, _, _, _, ho, K, P, A, Q, B, e, hK, hP, hB, seq, power, collapse, strength⟩ := h
  obtain ⟨hA, hQ, he⟩ : M.mem A X ∧ M.mem Q X ∧ M.mem e X := by
    obtain ⟨_, _, _, _, _, pool, _, _, _, hQ, he, _⟩ := collapse
    exact ⟨pool.carrier, hQ, he⟩
  obtain ⟨K', hK', hKK⟩ := hj.1.1.2.2 K hK
  obtain ⟨P', hP', hPP⟩ := hj.1.1.2.2 P hP
  obtain ⟨A', _, hAA⟩ := hj.1.1.2.2 A hA
  obtain ⟨Q', _, hQQ⟩ := hj.1.1.2.2 Q hQ
  obtain ⟨B', hB', hBB⟩ := hj.1.1.2.2 B hB
  obtain ⟨e', _, hee⟩ := hj.1.1.2.2 e he
  exact ⟨hj.1.1.output_mem_of_pairMember (hj.omega_l I hZF hω hX hY hm hn hωX),
    hj.1.1.output_mem_of_pairMember hκ, hj.1.1.output_mem_of_pairMember hL, hj.1.1.output_mem_of_pairMember hF,
    hj.ordinal_l hZF hω hX hY hm hn hL ho, K', P', A', Q', B', e', hK', hP', hB',
    hj.sequences_l hZF hω hX hY hm hn theory hωX hκ hKK seq,
    hj.power_l hZF hω hX hY hm hn hκ hPP power,
    collapse.map_l hZF hω hX hY hm hn hj theory hωX hκ hL hKK hPP hF hAA hQQ hBB hee,
    (es_strength_map_l hZF hω hX hY hm hn hj hL hBB).mp strength⟩

/-- 源内证书读取指定实际超幂的最大强度，不要求它在背景中不可达。 -/
theorem Ex_strength_d.realize_l (hZF : M.Models ZF) {ω κ K L X R F c d N S j Γ : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d N S)
    (ultra : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c d j) (hκ : M.TransitiveSet κ)
    (hκj : Rd_entry_d κ Γ j) (bound : M.MemberSubset L Γ)
    (h : Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X F) : Es_strength_d X L N := by
  obtain ⟨_, _, _, _, _, K₀, P, A, Q, Y, e, _, hP, _, seq, power, collapse, strength⟩ := h
  have eq := hZF.1.eq_of_same_members K₀ K (fun s => (seq s).trans ((source.finite_l (ZF.modelsKP hZF)) s).symm)
  subst K₀
  have trans : M.TransitiveSet P := by
    intro x hx y hy
    have hyκ := ((power x).mp hx).2 y hy
    exact (power y).mpr ⟨source.transitive κ source.cardinal_mem y hyκ, hκ y hyκ⟩
  have hPY := (collapse.image_l hZF source family hm hn ultra hP trans).1
  have hj := ultra.elementary_l hZF hm.1 hn.1
  have hN := ultra.transitive_l hZF hn.1
  have target := hj.power_l hZF source.omega source.transitive hN hm hn hκj hPY power
  refine ⟨fun α hα x hx sub => hN Y (hj.1.1.output_mem_of_pairMember hPY) x (strength.1 α hα x hx sub), ?_⟩
  obtain ⟨x, hx, sub, missing⟩ := strength.2
  exact ⟨x, hx, sub, fun hxN => missing ((target x).mpr ⟨hxN, fun y hy => bound y (sub y hy)⟩)⟩

theorem ep_exact_strength_l (hZFC : M.Models ZFC) {ω κ K L X R F δ V b d N S i Γ : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K X R)
    (hX : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ X) (hδ : M.IsLimitOrdinal δ)
    (hL : M.mem L δ) (hκL : M.mem κ L) (hωL : M.mem ω L)
    (hr : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) L)
    (hs : M.IsStrongLimitCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) L)
    (hV : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) L V)
    (family : Em_source_d ω κ L X F) (hF : M.mem F X)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) b X R)
    (hn : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d N S)
    (ultra : It_ultra_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L F b d i)
    (hκi : Rd_entry_d κ Γ i) (bound : M.MemberSubset L Γ) (cover : M.MemberSubset V N)
    (missing : ∃ x, M.MemberSubset x L ∧ ¬ M.mem x N) :
    Ex_strength_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F ∧ Er_level_d X L V := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hN := ultra.transitive_l hZF hn.1
  have hi := ultra.elementary_l hZF hm.1 hn.1
  have hLX := ZF.v_ordinal_mem_l I hZF hX hL
  have level := ep_relative_rank_l hZFC source hX hδ hL hωL hr hs hV
  have hκV := ZF.v_ordinal_mem_l I hZF hV hκL
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF κ
  have hPX := v_power_mem_l I hX hδ source.cardinal_mem hP
  have trans : M.TransitiveSet P := fun x hx y hy => (hP y).mpr
    ((hr.isCardinal.1.mem hκL).transitive y ((hP x).mp hx y hy))
  obtain ⟨Y, hYN, hPY⟩ := hi.1.1.2.2 P hPX
  obtain ⟨hYX, A, Q, e, collapse⟩ := it_ultra_owned_image_l hZF source (sc_v_power_l (ZF.modelsKP hZF) hδ hX)
    family hm hn ultra hLX hF hr.isLimitOrdinal level hκV
    (v_power_mem_l I hV hr.isLimitOrdinal hκV hP) trans hPY
  have powers : FilterZF.Source_d X κ P := fun x =>
    ⟨fun hx => ⟨source.transitive P hPX x hx, (hP x).mp hx⟩, fun ⟨_, hx⟩ => (hP x).mpr hx⟩
  have power := hi.power_l hZF source.omega source.transitive hN hm hn hκi hPY powers
  refine ⟨⟨source.omega_mem, source.cardinal_mem, hLX, hF, hr.isCardinal.1,
    K, P, A, Q, Y, e, source.finite.mem_l, hPX, hYX, (source.finite_l (ZF.modelsKP hZF)), powers, collapse, ?_, ?_⟩, level⟩
  · intro α hα x _ sub
    have hxN := cover x (v_subset_mem_l I hV (ZF.v_ordinal_mem_l I hZF hV hα) sub)
    exact (power x).mpr ⟨hxN, fun y hy => bound y (hr.isCardinal.1.transitive α hα y (sub y hy))⟩
  · obtain ⟨x, sub, hx⟩ := missing
    exact ⟨x, v_subset_mem_l I hX hLX sub, sub, fun h => hx (hN Y hYN x h)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原关系后继中的最大子集覆盖

子集的实现由全部成员及其原坐标确定。完整前驱图与容器的子集闭包保证：
目标中的任意实现都必须回到原有界像。因此原缺失子集在整个后继中没有实现。
这条结论只用所属结构的外延性，不要求原迭代模型在背景中传递。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 原对象的全部成员经同一坐标图实现为目标对象的全部成员。 -/
def Er_rep_d (N R C W t x E : M.Domain) : Prop :=
  M.mem x N ∧ M.mem E C ∧ ∀ P, Rd_entry_d P E W ↔
    ∃ a, M.mem a N ∧ Rd_entry_d a x R ∧ Rd_entry_d a P t

def er_rep_m {d} (N R C W t x E : Term d) : Formula 1 d := set[d] ⟪
  ⌜x⌝ₛ ∈ ⌜N⌝ₛ ∧ ⌜E⌝ₛ ∈ ⌜C⌝ₛ ∧
  (∀ P, ⌜rd_entry0_m⌝ₚ(P, ⌜E⌝ₛ, ⌜W⌝ₛ) ↔
    ∃ a ∈ ⌜N⌝ₛ, ⌜rd_entry0_m⌝ₚ(a, ⌜x⌝ₛ, ⌜R⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(a, P, ⌜t⌝ₛ))⟫
derive_free_closed er_rep_m

theorem er_rep_sat_l (hE : Extensional M) {d} (ρ : Env M d) (N R C W t x E : Term d) :
    Formula.satisfies ρ (er_rep_m N R C W t x E) ↔
      Er_rep_d (N.eval ρ) (R.eval ρ) (C.eval ρ) (W.eval ρ) (t.eval ρ) (x.eval ρ) (E.eval ρ) := by
  simp only [er_rep_m, Er_rep_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_existsMem_iff,
    rd_entry0_sat_l hE, Definitional.Term.eval_weaken]; rfl

/-- 覆盖原模型在支撑以下的全部子集，并在支撑处给出全目标范围的缺失见证。 -/
def Er_exact_d (N R C W L t : M.Domain) : Prop := M.mem L N ∧
  (∀ α, M.mem α N → Rd_entry_d α L R → ∀ x, M.mem x N →
    (∀ a, M.mem a N → Rd_entry_d a x R → Rd_entry_d a α R) →
      ∃ E, Er_rep_d N R C W t x E) ∧
  ∃ x, M.mem x N ∧ (∀ a, M.mem a N → Rd_entry_d a x R → Rd_entry_d a L R) ∧
    ∀ E, ¬ Er_rep_d N R C W t x E

def er_exact_m {d} (N R C W L t : Term d) : Formula 1 d := set[d] ⟪
  ⌜L⌝ₛ ∈ ⌜N⌝ₛ ∧
  (∀ α ∈ ⌜N⌝ₛ, ⌜rd_entry0_m⌝ₚ(α, ⌜L⌝ₛ, ⌜R⌝ₛ) → ∀ x ∈ ⌜N⌝ₛ,
    (∀ a ∈ ⌜N⌝ₛ, ⌜rd_entry0_m⌝ₚ(a, x, ⌜R⌝ₛ) → ⌜rd_entry0_m⌝ₚ(a, α, ⌜R⌝ₛ)) →
      ∃ E, ⌜er_rep_m⌝ₚ(⌜N⌝ₛ, ⌜R⌝ₛ, ⌜C⌝ₛ, ⌜W⌝ₛ, ⌜t⌝ₛ, x, E)) ∧
  (∃ x ∈ ⌜N⌝ₛ,
    (∀ a ∈ ⌜N⌝ₛ, ⌜rd_entry0_m⌝ₚ(a, x, ⌜R⌝ₛ) → ⌜rd_entry0_m⌝ₚ(a, ⌜L⌝ₛ, ⌜R⌝ₛ)) ∧
    (∀ E, ¬ ⌜er_rep_m⌝ₚ(⌜N⌝ₛ, ⌜R⌝ₛ, ⌜C⌝ₛ, ⌜W⌝ₛ, ⌜t⌝ₛ, x, E)))⟫
derive_free_closed er_exact_m

theorem er_exact_sat_l (hE : Extensional M) {d} (ρ : Env M d) (N R C W L t : Term d) :
    Formula.satisfies ρ (er_exact_m N R C W L t) ↔
      Er_exact_d (N.eval ρ) (R.eval ρ) (C.eval ρ) (W.eval ρ) (L.eval ρ) (t.eval ρ) := by
  simp only [er_exact_m, Er_exact_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_exists_iff, Formula.satisfies_neg_iff,
    rd_entry0_sat_l hE, er_rep_sat_l hE, Definitional.Term.eval_weaken]; rfl

variable (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP

/-- 子集闭包把任意目标实现收回同一实现图，外延性识别原对象。 -/
theorem er_subset_read_l {N R C W Γ t H l : M.Domain}
    (nx : ∃ x, M.mem x N) (ext : Extensional (smdl_structure_l I (R := R) nx))
    (Y L : (smdl_structure_l I (R := R) nx).Domain)
    (trans : (smdl_structure_l I (R := R) nx).TransitiveSet Y)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x Y.val R)
    (ft : M.IsSetInjectionFromTo I t Γ C)
    (image : ∀ E, Rd_entry_d E H W ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x E t)
    (pred : ∀ x E, Rd_entry_d x E t → ∀ P,
      Rd_entry_d P E W ↔ ∃ a, Rd_entry_d a x R ∧ Rd_entry_d a P t)
    (closed : Rr_closed_d I C W H) (hL : Rd_entry_d L.val l t) :
    ∀ x : (smdl_structure_l I (R := R) nx).Domain, ∀ E,
      (smdl_structure_l I (R := R) nx).MemberSubset x L →
        (Er_rep_d N R C W t x.val E ↔ Rd_entry_d x.val E t) := by
  let N₀ := smdl_structure_l I (R := R) nx
  have entry (x : N₀.Domain) E (hx : Rd_entry_d x.val E t) : Er_rep_d N R C W t x.val E := by
    refine ⟨x.property, ft.1.output_mem_of_pairMember hx, fun P => ?_⟩
    apply (pred x.val E hx P).trans
    constructor
    · rintro ⟨a, ha, hp⟩
      exact ⟨a, ((carrier a).mp (ft.1.input_mem_of_pairMember hp)).1, ha, hp⟩
    · rintro ⟨a, _, ha, hp⟩
      exact ⟨a, ha, hp⟩
  have hLY : N₀.mem L Y := ((carrier L.val).mp (ft.1.input_mem_of_pairMember hL)).2
  intro x E sub
  refine ⟨fun rep => ?_, entry x E⟩
  have hEH := closed l E (ft.1.output_mem_of_pairMember hL) rep.2.1
    ((image l).mpr ⟨L.val, ft.1.input_mem_of_pairMember hL, hL⟩) (fun P _ hPE => by
      obtain ⟨a, ha, hax, haP⟩ := (rep.2.2 P).mp hPE
      exact (pred L.val l hL P).mpr ⟨a, sub ⟨a, ha⟩ hax, haP⟩)
  obtain ⟨y, hy, hyE⟩ := (image E).mp hEH
  let y' : N₀.Domain := ⟨y, ((carrier y).mp hy).1⟩
  have same : x = y' := ext.eq_of_same_members x y' (fun a => by
    have read (haY : N₀.mem a Y) : N₀.mem a x ↔ N₀.mem a y' := by
      obtain ⟨P, _, haP⟩ := ft.1.2.2 a.val ((carrier a.val).mpr ⟨a.property, haY⟩)
      constructor
      · intro ha
        obtain ⟨b, hb, hbP⟩ := (pred y E hyE P).mp ((rep.2.2 P).mpr ⟨a.val, a.property, ha, haP⟩)
        change Rd_entry_d a.val y R
        exact ft.2 b a.val P hbP haP ▸ hb
      · intro ha
        obtain ⟨b, _, hb, hbP⟩ := (rep.2.2 P).mp ((pred y E hyE P).mpr ⟨a.val, ha, haP⟩)
        change Rd_entry_d a.val x.val R
        exact ft.2 b a.val P hbP haP ▸ hb
    exact ⟨fun ha => (read (trans L hLY a (sub a ha))).mp ha,
      fun ha => (read (trans y' ((carrier y).mp hy).2 a ha)).mpr ha⟩)
  exact (congrArg Subtype.val same).symm ▸ hyE

theorem er_exact_l {N R C W Γ t H l : M.Domain}
    (nx : ∃ x, M.mem x N) (ext : Extensional (smdl_structure_l I (R := R) nx))
    (X Y L : (smdl_structure_l I (R := R) nx).Domain)
    (trans : (smdl_structure_l I (R := R) nx).TransitiveSet Y)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x Y.val R)
    (ft : M.IsSetInjectionFromTo I t Γ C)
    (image : ∀ E, Rd_entry_d E H W ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x E t)
    (pred : ∀ x E, Rd_entry_d x E t → ∀ P,
      Rd_entry_d P E W ↔ ∃ a, Rd_entry_d a x R ∧ Rd_entry_d a P t)
    (closed : Rr_closed_d I C W H) (hL : Rd_entry_d L.val l t)
    (ord : (smdl_structure_l I (R := R) nx).TransitiveSet L)
    (cover : ∀ α x : (smdl_structure_l I (R := R) nx).Domain,
      (smdl_structure_l I (R := R) nx).mem α L →
      (smdl_structure_l I (R := R) nx).MemberSubset x α → (smdl_structure_l I (R := R) nx).mem x X)
    (strength : Es_strength_d X L Y) : Er_exact_d N R C W L.val t := by
  have read := er_subset_read_l hKP nx ext Y L trans carrier ft image pred closed hL
  refine ⟨L.property, ?_, ?_⟩
  · intro α hα hαL x hx sub
    let a := (⟨α, hα⟩ : (smdl_structure_l I (R := R) nx).Domain)
    let b := (⟨x, hx⟩ : (smdl_structure_l I (R := R) nx).Domain)
    have lower : (smdl_structure_l I (R := R) nx).MemberSubset b a := fun y => sub y.val y.property
    obtain ⟨E, _, hxE⟩ := ft.1.2.2 x ((carrier x).mpr ⟨hx, strength.1 a hαL b (cover a b hαL lower) lower⟩)
    exact ⟨E, (read b E (fun y hy => ord a hαL y (lower y hy))).mpr hxE⟩
  · obtain ⟨x, _, sub, missing⟩ := strength.2
    refine ⟨x.val, x.property, fun a ha => sub ⟨a, ha⟩, fun E rep => ?_⟩
    exact missing ((carrier x.val).mp (ft.1.input_mem_of_pairMember ((read x E sub).mp rep))).2

/-- 完整子集实现只使用其成员坐标，限制图时逐点保持。 -/
theorem er_rep_restrict_l {N R C W t D u x E : M.Domain}
    (res : M.IsRestrictionOf I u t D)
    (inside : ∀ a, M.mem a N → Rd_entry_d a x R → M.mem a D) :
    Er_rep_d N R C W u x E ↔ Er_rep_d N R C W t x E := by
  have graph a P (ha : M.mem a N) (hax : Rd_entry_d a x R) :
      Rd_entry_d a P u ↔ Rd_entry_d a P t :=
    (res.2 a P).trans (and_iff_right (inside a ha hax))
  unfold Er_rep_d
  exact and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun P =>
    iff_congr Iff.rfl (exists_congr fun a => and_congr_right fun ha =>
      and_congr_right fun hax => graph a P ha hax)

/-- 子集实现只使用支撑以下的成员坐标，故限制到共同秩段后保持同一缺失见证。 -/
theorem Er_exact_d.restrict_l {N R C W t D u : M.Domain}
    (nx : ∃ x, M.mem x N) (L : (smdl_structure_l I (R := R) nx).Domain)
    (ord : (smdl_structure_l I (R := R) nx).TransitiveSet L)
    (res : M.IsRestrictionOf I u t D)
    (inside : ∀ a, M.mem a N → Rd_entry_d a L.val R → M.mem a D)
    (h : Er_exact_d N R C W L.val t) : Er_exact_d N R C W L.val u := by
  have read x E (sub : ∀ a, M.mem a N → Rd_entry_d a x R → Rd_entry_d a L.val R) :=
    er_rep_restrict_l hKP (C := C) (W := W) (x := x) (E := E) res (fun a ha hax => inside a ha (sub a ha hax))
  refine ⟨h.1, ?_, ?_⟩
  · intro α hα hαL x hx sub
    obtain ⟨E, rep⟩ := h.2.1 α hα hαL x hx sub
    exact ⟨E, (read x E (fun a ha hax => ord ⟨α, hα⟩ hαL ⟨a, ha⟩ (sub a ha hax))).mpr rep⟩
  · obtain ⟨x, hx, sub, missing⟩ := h.2.2
    exact ⟨x, hx, sub, fun E rep => missing E ((read x E sub).mp rep)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 较高共同层保持原子集的全局实现与缺失

较早支撑的端点属于新共同层时，任意新实现都被新容器的子集闭包回收。
两张完整前驱图的复合因此双向保持实现存在性，并保留同一个缺失子集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP

theorem er_rep_comp_l {X R N S C W D t s v x E F : M.Domain}
    (fs : M.IsSetInjectionFromTo I s D C) (domain : M.MemberSubset D N)
    (down : ∀ a b, M.mem a D → Rd_entry_d b a S → M.mem b D)
    (inside : ∀ a b, Rd_entry_d a b t → M.mem b D)
    (pred : ∀ a b, Rd_entry_d a b s → ∀ P,
      Rd_entry_d P b W ↔ ∃ y, Rd_entry_d y a S ∧ Rd_entry_d y P s)
    (comp : It_comp_d t s v) (hEF : Rd_entry_d E F s) :
    Er_rep_d X R N S t x E ↔ Er_rep_d X R C W v x F := by
  constructor
  · rintro ⟨hx, _, rep⟩
    refine ⟨hx, fs.1.output_mem_of_pairMember hEF, fun P => ?_⟩
    constructor
    · intro hPF
      obtain ⟨B, hBE, hBP⟩ := (pred E F hEF P).mp hPF
      obtain ⟨a, ha, hax, haB⟩ := (rep B).mp hBE
      exact ⟨a, ha, hax, (comp.2 a P).mpr ⟨B, haB, hBP⟩⟩
    · rintro ⟨a, ha, hax, haP⟩
      obtain ⟨B, haB, hBP⟩ := (comp.2 a P).mp haP
      exact (pred E F hEF P).mpr ⟨B, (rep B).mpr ⟨a, ha, hax, haB⟩, hBP⟩
  · rintro ⟨hx, _, rep⟩
    refine ⟨hx, domain E (fs.1.input_mem_of_pairMember hEF), fun B => ?_⟩
    constructor
    · intro hBE
      obtain ⟨P, _, hBP⟩ := fs.1.2.2 B (down E B (fs.1.input_mem_of_pairMember hEF) hBE)
      obtain ⟨a, ha, hax, haP⟩ := (rep P).mp ((pred E F hEF P).mpr ⟨B, hBE, hBP⟩)
      obtain ⟨B', haB, hB'P⟩ := (comp.2 a P).mp haP
      exact ⟨a, ha, hax, fs.2 B' B P hB'P hBP ▸ haB⟩
    · rintro ⟨a, ha, hax, haB⟩
      obtain ⟨P, _, hBP⟩ := fs.1.2.2 B (inside a B haB)
      obtain ⟨B', hB'E, hB'P⟩ := (pred E F hEF P).mp
        ((rep P).mpr ⟨a, ha, hax, (comp.2 a P).mpr ⟨B, haB, hBP⟩⟩)
      exact fs.2 B' B P hB'P hBP ▸ hB'E

/-- 量化整个目标的实现存在性在复合图下双向保持。 -/
theorem er_rep_exists_comp_l {X R N S C W D t s v U H L ρ x : M.Domain}
    (fs : M.IsSetInjectionFromTo I s D C)
    (carrier : ∀ a, M.mem a D ↔ M.mem a N ∧ Rd_entry_d a U S)
    (down : ∀ a b, M.mem a D → Rd_entry_d b a S → M.mem b D)
    (inside : ∀ a b, Rd_entry_d a b t → M.mem b D)
    (image : ∀ E, Rd_entry_d E H W ↔ ∃ a, M.mem a D ∧ Rd_entry_d a E s)
    (pred : ∀ a b, Rd_entry_d a b s → ∀ P,
      Rd_entry_d P b W ↔ ∃ y, Rd_entry_d y a S ∧ Rd_entry_d y P s)
    (leftClosed : Rr_closed_d I N S U) (rightClosed : Rr_closed_d I C W H)
    (comp : It_comp_d t s v) (hρ : M.mem ρ D) (endpt : Er_rep_d X R N S t L ρ)
    (sub : ∀ a, M.mem a X → Rd_entry_d a x R → Rd_entry_d a L R) :
    (∃ E, Er_rep_d X R N S t x E) ↔ ∃ F, Er_rep_d X R C W v x F := by
  have domain a ha := ((carrier a).mp ha).1
  have read {x E F : M.Domain} (hEF : Rd_entry_d E F s) :=
    er_rep_comp_l hKP (X := X) (R := R) (x := x) fs domain down inside pred comp hEF
  obtain ⟨l, hl, hρl⟩ := fs.1.2.2 ρ hρ
  have endpoint := (read (x := L) hρl).mp endpt
  constructor
  · rintro ⟨E, rep⟩
    have hEU := leftClosed ρ E (domain ρ hρ) rep.2.1 ((carrier ρ).mp hρ).2 (fun P _ hPE => by
      obtain ⟨a, ha, hax, haP⟩ := (rep.2.2 P).mp hPE
      exact (endpt.2.2 P).mpr ⟨a, ha, sub a ha hax, haP⟩)
    obtain ⟨F, _, hEF⟩ := fs.1.2.2 E ((carrier E).mpr ⟨rep.2.1, hEU⟩)
    exact ⟨F, (read hEF).mp rep⟩
  · rintro ⟨F, rep⟩
    have hFH := rightClosed l F hl rep.2.1 ((image l).mpr ⟨ρ, hρ, hρl⟩) (fun P _ hPF => by
      obtain ⟨a, ha, hax, haP⟩ := (rep.2.2 P).mp hPF
      exact (endpoint.2.2 P).mpr ⟨a, ha, sub a ha hax, haP⟩)
    obtain ⟨E, _, hEF⟩ := (image F).mp hFH
    exact ⟨E, (read hEF).mpr rep⟩

theorem Er_exact_d.comp_l {X R N S C W D t s v U H L ρ : M.Domain}
    (fs : M.IsSetInjectionFromTo I s D C)
    (carrier : ∀ a, M.mem a D ↔ M.mem a N ∧ Rd_entry_d a U S)
    (down : ∀ a b, M.mem a D → Rd_entry_d b a S → M.mem b D)
    (inside : ∀ a b, Rd_entry_d a b t → M.mem b D)
    (image : ∀ E, Rd_entry_d E H W ↔ ∃ a, M.mem a D ∧ Rd_entry_d a E s)
    (pred : ∀ a b, Rd_entry_d a b s → ∀ P,
      Rd_entry_d P b W ↔ ∃ y, Rd_entry_d y a S ∧ Rd_entry_d y P s)
    (leftClosed : Rr_closed_d I N S U) (rightClosed : Rr_closed_d I C W H)
    (comp : It_comp_d t s v) (hρ : M.mem ρ D) (endpt : Er_rep_d X R N S t L ρ)
    (trans : ∀ a b, M.mem a X → M.mem b X → Rd_entry_d a L R → Rd_entry_d b a R → Rd_entry_d b L R)
    (h : Er_exact_d X R N S L t) : Er_exact_d X R C W L v := by
  have read {x : M.Domain} (sub : ∀ a, M.mem a X → Rd_entry_d a x R → Rd_entry_d a L R) :=
    er_rep_exists_comp_l hKP fs carrier down inside image pred leftClosed rightClosed comp hρ endpt sub
  refine ⟨h.1, ?_, ?_⟩
  · intro α hα hαL x hx sub
    exact (read (x := x) (fun a ha hax => trans α a hα ha hαL (sub a ha hax))).mp
      (h.2.1 α hα hαL x hx sub)
  · obtain ⟨x, hx, sub, missing⟩ := h.2.2
    exact ⟨x, hx, sub, fun F rep => by
      obtain ⟨E, old⟩ := (read sub).mpr ⟨F, rep⟩
      exact missing E old⟩

end YesMetaZFC.SetTheory.LargeCardinal
