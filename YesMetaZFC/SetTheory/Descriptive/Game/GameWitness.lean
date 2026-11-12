import YesMetaZFC.SetTheory.Descriptive.Game.GameShift
import YesMetaZFC.Model.SetTheory.Images.OrdinalSequenceImage
import YesMetaZFC.SetTheory.Descriptive.Coding.FunctionCode
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph
import YesMetaZFC.Model.SetTheory.Truth.SetTruthReals

/-! # 全部有限局面的规范自然数编号

长度及序数折叠值共同编码每个内部有限局面；编号是实际单射图。
成员满嵌入运输同一编码，唯一性使不同模型的编号可直接比较。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

structure Gs_number_d (ω T E : M.Domain) : Prop where
  function : M.IsSetInjectionFromTo I E T ω
  codes : ∀ s n, M.PairMember I s n E ↔ M.mem s T ∧ Oc_seq_d I ω s n

theorem gs_number_exists_l (hZF : M.Models ZF) {ω T : M.Domain} (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω ω T) : ∃ E, Gs_number_d I ω T E := by
  obtain ⟨C,E,_,_,bij,_,codes,_⟩ := oc_seq_tables_l I hZF hw (hw.isOrdinal (ZF.modelsKP hZF)) space
  refine ⟨E,⟨⟨bij.1.1.1,bij.1.1.2.1,?_⟩,bij.1.2⟩,codes⟩
  intro s hs
  obtain ⟨n,_,sn⟩ := bij.1.1.2.2 s hs
  obtain ⟨k,hk,fn⟩ := (space s).mp hs
  exact ⟨n,oc_seq_natural_l I hZF hw fn ((codes s n).mp sn).2,sn⟩

theorem Gs_number_d.unique_l (hE : Extensional M) {ω T E F : M.Domain}
    (left : Gs_number_d I ω T E) (right : Gs_number_d I ω T F) : E = F :=
  left.function.1.1.1.eq_of_pairMember_iff hE right.function.1.1.1
    (fun s n => (left.codes s n).trans (right.codes s n).symm)

omit I in
theorem Gs_number_d.image_l {N : Structure.{v}} (hM : M.Models ZF) (hN : N.Models ZF)
    (e : M.Domain → N.Domain) (ei : Function.Injective e)
    (ef : ∀ a y, N.mem y (e a) ↔ ∃ b, M.mem b a ∧ e b = y)
    {ω T E : M.Domain} (hw : M.IsOmega ω) (number : Gs_number_d (kp_pair_l (ZF.modelsKP hM)) ω T E) :
    Gs_number_d (kp_pair_l (ZF.modelsKP hN)) (e ω) (e T) (e E) := by
  have fn := image_injection_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e ei ef number.function
  refine ⟨fn,fun s n => ⟨?_,?_⟩⟩
  · intro sn
    obtain ⟨s₀,n₀,edge,rfl,rfl⟩ := (image_entries_l e ef number.function.1.1.1 s n).mp sn
    exact ⟨(image_member_l e ei ef).mpr ((number.codes s₀ n₀).mp edge).1,
      oc_seq_image_l hM hN e ei ef hw ((number.codes s₀ n₀).mp edge).2⟩
  · rintro ⟨hs,code⟩
    obtain ⟨s₀,hs₀,rfl⟩ := (ef T s).mp hs
    obtain ⟨n₀,_,sn⟩ := number.function.1.2.2 s₀ hs₀
    have moved := oc_seq_image_l hM hN e ei ef hw ((number.codes s₀ n₀).mp sn).2
    have eq := oc_seq_unique_l (kp_pair_l (ZF.modelsKP hN)) hN moved code
    exact eq ▸ (image_entry_iff_l e ei ef (KP.exists_pair (ZF.modelsKP hM)) hN.1 s₀ n₀ E).mp sn

end YesMetaZFC.SetTheory.Descriptive

/-! ## 自然数博弈的全部策略由实数编码

局面空间的规范有限序列编号用于读取实数坐标。每个实数解码为一个完整策略，
每个完整策略都由一个实数表示；偶数回合集合也由原公式分离构造。
后续有界决定性公式只使用这些实际数据，不量化无界策略空间。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Gs_decode_d (ω T E r σ : M.Domain) : Prop := M.IsSetFunctionFromTo I σ T ω ∧
  ∀ s v, M.mem s T → (Nv_d I E r s v ↔ M.PairMember I s v σ)

theorem gs_decode_l (hZF : M.Models ZF) {ω T E r : M.Domain}
    (index : M.IsSetFunctionFromTo I E T ω) (real : M.IsSetFunctionFromTo I r ω ω) :
    ∃ σ, Gs_decode_d I ω T E r σ := by
  obtain ⟨σ,fn,edges⟩ := ZF.exists_compositionFunction hZF I index real
  exact ⟨σ,fn,fun s v hs =>
    ⟨fun h => (edges s v).mpr ⟨hs,h⟩,fun h => ((edges s v).mp h).2⟩⟩

theorem gs_encode_l (hZF : M.Models ZF) {ω B T E σ : M.Domain} (space : Baire_d I ω B)
    (index : M.IsSetInjectionFromTo I E T ω) (strategy : M.IsSetFunctionFromTo I σ T ω) :
    ∃ r, M.mem r B ∧ Gs_decode_d I ω T E r σ := by
  obtain ⟨z,_,hz⟩ := space.1.1.1
  obtain ⟨r,real,read⟩ := nv_encode_l I hZF index strategy hz
  exact ⟨r,(space.2 r).mpr real,strategy,read⟩

/-- 两份编码基础数据均由原博弈空间自动构造。 -/
theorem gs_setup_l (hZF : M.Models ZF) {ω T : M.Domain} (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω ω T) :
    ∃ E V, Gs_number_d I ω T E ∧ M.MemberSubset V ω ∧
      ∀ n, M.mem n ω → (M.mem n V ↔ Gm_even_d I ω n) := by
  obtain ⟨E,index⟩ := gs_number_exists_l I hZF hw space
  let ρ : Env M 1 := ⟨fun _ => ω,fun _ => ω⟩
  let φ : UnarySchema 1 := { body := gm_even_m (𝒞 := 𝒞) (.bound 1) .newest }
  obtain ⟨V,sep⟩ := ZF.separation_exists_d hZF φ ρ ω
  have read n : M.mem n V ↔ M.mem n ω ∧ Gm_even_d I ω n :=
    (sep n).trans (and_congr_right fun _ => gm_even_sat_l I hZF.1 _ _ _)
  exact ⟨E,V,index,fun n hn => ((read n).mp hn).1,fun n hn => (read n).trans (and_iff_right hn)⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 博弈基础数据的有界识别

完整实数族下，有限局面空间只需逐项有限性和全部实数前缀覆盖。
编号检查为有界单射图；奇偶集合由零和后继翻转作内部归纳识别。
三项均为 Δ₀，不要求见证集合满足任何集合论。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Gs_space_d (ω B T : M.Domain) : Prop :=
  (∀ t, M.mem t T → ∃ n, M.mem n ω ∧ Fn0_d n ω t) ∧
    ∀ r, M.mem r B → ∀ n, M.mem n ω → ∃ t, M.mem t T ∧ Fn0_d n ω t ∧ M.MemberSubset t r

def gs_space_m {d} (ω B T : Term d) : Formula 1 d := set[d] ⟪
  (∀ t ∈ ⌜T⌝ₛ, ∃ n ∈ ⌜ω⌝ₛ, ⌜fn0_m⌝ₚ(n,⌜ω⌝ₛ,t)) ∧
  (∀ r ∈ ⌜B⌝ₛ, ∀ n ∈ ⌜ω⌝ₛ, ∃ t ∈ ⌜T⌝ₛ, ⌜fn0_m⌝ₚ(n,⌜ω⌝ₛ,t) ∧ t ⊆ r)⟫
derive_free_closed gs_space_m

theorem gs_space_delta_l {d} (ω B T : Term d) : (gs_space_m ω B T).IsDelta0 :=
  .conj (.forallMem _ (.existsMem _ (fn0_delta_l ..)))
    (.forallMem _ (.forallMem _ (.existsMem _ (.conj (fn0_delta_l ..) (.atom _ _ _)))))

theorem gs_space_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω B T : Term d) :
    Formula.satisfies ρ (gs_space_m ω B T) ↔ Gs_space_d (ω.eval ρ) (B.eval ρ) (T.eval ρ) := by
  simp only [gs_space_m,Gs_space_d,Formula.satisfies_conj_iff,Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff,fn0_sat_l hE,Formula.satisfies_subset_iff,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  rfl

theorem gs_space_iff_l (hZF : M.Models ZF) {ω B T : M.Domain}
    (space : Baire_d (kp_pair_l (ZF.modelsKP hZF)) ω B) :
    Gs_space_d ω B T ↔ Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  constructor
  · intro h t
    constructor
    · intro ht
      obtain ⟨n,hn,fn⟩ := h.1 t ht
      exact ⟨n,hn,fn0_function_l (ZF.modelsKP hZF) fn⟩
    · rintro ⟨n,hn,fn⟩
      obtain ⟨z,_,hz⟩ := space.1.1.1
      obtain ⟨r,fr,cut,_⟩ := ds_extend_l I hZF space.1 hn fn hz
      obtain ⟨s,hs,fs,sub⟩ := h.2 r ((space.2 r).mpr fr) n hn
      have eq := ((ds_restrict_iff_l I (fn0_function_l (ZF.modelsKP hZF) fs) fr.1).mpr sub).eq hZF.1 cut
      exact eq ▸ hs
  · intro finite
    refine ⟨fun t ht => ((finite t).mp ht).imp fun n h => ⟨h.1,fn0_of_function_l (ZF.modelsKP hZF) h.2⟩,?_⟩
    intro r hr n hn
    have fr := (space.2 r).mp hr
    obtain ⟨t,ft,cut,_⟩ := ds_prefix_l I hZF space.1 fr hn
    exact ⟨t,(finite t).mpr ⟨n,hn,ft⟩,fn0_of_function_l (ZF.modelsKP hZF) ft,(ds_restrict_iff_l I ft fr.1).mp cut⟩

def Gs_index_d (ω T E : M.Domain) : Prop := Fn0_d T ω E ∧
  ∀ s, M.mem s T → ∀ t, M.mem t T → ∀ i, M.mem i ω → Rd_entry_d s i E → Rd_entry_d t i E → s = t

def gs_index_m {d} (ω T E : Term d) : Formula 1 d := set[d] ⟪
  ⌜fn0_m⌝ₚ(⌜T⌝ₛ,⌜ω⌝ₛ,⌜E⌝ₛ) ∧ (∀ s ∈ ⌜T⌝ₛ, ∀ t ∈ ⌜T⌝ₛ, ∀ i ∈ ⌜ω⌝ₛ,
    ⌜rd_entry0_m⌝ₚ(s,i,⌜E⌝ₛ) → ⌜rd_entry0_m⌝ₚ(t,i,⌜E⌝ₛ) → s = t)⟫
derive_free_closed gs_index_m

theorem gs_index_delta_l {d} (ω T E : Term d) : (gs_index_m ω T E).IsDelta0 :=
  .conj (fn0_delta_l ..) (.forallMem _ (.forallMem _ (.forallMem _
    (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (.atom _ _ _))))))

theorem gs_index_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω T E : Term d) :
    Formula.satisfies ρ (gs_index_m ω T E) ↔ Gs_index_d (ω.eval ρ) (T.eval ρ) (E.eval ρ) := by
  simp only [gs_index_m,Gs_index_d,Formula.satisfies_conj_iff,fn0_sat_l hE,Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff,rd_entry0_sat_l hE,Formula.satisfies_extensionalEq_iff_eq hE,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

theorem gs_index_iff_l (hKP : M.Models KP) {ω T E : M.Domain} :
    Gs_index_d ω T E ↔ M.IsSetInjectionFromTo (kp_pair_l hKP) E T ω :=
  ⟨fun h => ⟨fn0_function_l hKP h.1,fun s t i si ti =>
    h.2 s (h.1.bound_l si).1 t (h.1.bound_l ti).1 i (h.1.bound_l si).2 si ti⟩,
    fun h => ⟨fn0_of_function_l hKP h.1,fun s _ t _ i _ => h.2 s t i⟩⟩

def Gs_parity_d (ω V : M.Domain) : Prop :=
  (∀ n, M.mem n ω → (∀ x, ¬ M.mem x n) → M.mem n V) ∧
    ∀ n, M.mem n ω → ∀ m, M.mem m ω → M.SuccessorOf m n → (M.mem m V ↔ ¬ M.mem n V)

def gs_parity_m {d} (ω V : Term d) : Formula 1 d := set[d] ⟪
  (∀ n ∈ ⌜ω⌝ₛ, (∀ x ∈ n, ⊥) → n ∈ ⌜V⌝ₛ) ∧
  (∀ n ∈ ⌜ω⌝ₛ, ∀ m ∈ ⌜ω⌝ₛ, ⌜KP.succ0_m⌝ₚ(m,n) → (m ∈ ⌜V⌝ₛ ↔ ¬ n ∈ ⌜V⌝ₛ))⟫
derive_free_closed gs_parity_m

theorem gs_parity_delta_l {d} (ω V : Term d) : (gs_parity_m ω V).IsDelta0 :=
  .conj (.forallMem _ (.imp (.forallMem _ .falsum) (.mem _ _)))
    (.forallMem _ (.forallMem _ (.imp (KP.succ0_delta_l ..) (.iff (.mem _ _) (.neg (.mem _ _))))))

theorem gs_parity_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω V : Term d) :
    Formula.satisfies ρ (gs_parity_m ω V) ↔ Gs_parity_d (ω.eval ρ) (V.eval ρ) := by
  simp only [gs_parity_m,Gs_parity_d,Formula.satisfies_conj_iff,Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff,Formula.satisfies_falsum_iff,Formula.satisfies_mem_iff,KP.succ0_sat_l hE,
    Formula.satisfies_iff_iff,Formula.satisfies_neg_iff,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

/-- 原自然数上的可定义归纳把局部翻转条件识别为原加法定义的偶数。 -/
theorem gs_parity_iff_l (hZF : M.Models ZF) {ω V : M.Domain} (hw : M.IsOmega ω) :
    Gs_parity_d ω V ↔ ∀ n, M.mem n ω → (M.mem n V ↔ Gm_even_d (kp_pair_l (ZF.modelsKP hZF)) ω n) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  constructor
  · intro h
    let ρ : Env M 2 := ⟨Fin.cases ω (fun _ => V),fun _ => ω⟩
    let φ : UnarySchema 2 := { body := (.iff (.mem .newest (.bound 2))
      (gm_even_m (𝒞 := kpair_convention_l) (.bound 1) .newest)) }
    have sat n : φ.denote ρ n ↔ (M.mem n V ↔ Gm_even_d I ω n) := by
      simp only [φ,UnarySchema.denote,Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,gm_even_sat_l I hZF.1]; rfl
    obtain ⟨A,ha⟩ := ZF.separation_exists_d hZF φ ρ ω
    apply hw.induction _ ⟨A,fun n => (ha n).trans (and_congr_right fun _ => sat n)⟩
    · intro z hz
      obtain ⟨e,he,heω⟩ := hw.1.1
      have eq := hZF.1.eq_of_same_members e z (fun a => iff_of_false (he a) (hz a))
      exact iff_of_true (h.1 z (eq ▸ heω) hz) (gm_even_zero_l I hZF hw hz)
    · intro n hn ih m succ
      obtain ⟨v,hv,hvω⟩ := hw.1.2 n hn
      have hm : M.mem m ω := Structure.SuccessorOf.eq hZF.1 hv succ ▸ hvω
      exact (h.2 n hn m hm succ).trans ((not_congr ih).trans (gm_even_successor_l I hZF hw hn succ).symm)
  · intro parity
    exact ⟨fun n hn hz => (parity n hn).mpr (gm_even_zero_l I hZF hw hz),fun n hn m hm succ =>
      (parity m hm).trans ((gm_even_successor_l I hZF hw hn succ).trans (not_congr (parity n hn)).symm)⟩

def Gs_base_d (ω B T E V : M.Domain) : Prop := Gs_space_d ω B T ∧ Gs_index_d ω T E ∧ Gs_parity_d ω V

def gs_base_m {d} (ω B T E V : Term d) : Formula 1 d :=
  .conj (gs_space_m ω B T) (.conj (gs_index_m ω T E) (gs_parity_m ω V))
derive_free_closed gs_base_m

theorem gs_base_delta_l {d} (ω B T E V : Term d) : (gs_base_m ω B T E V).IsDelta0 :=
  .conj (gs_space_delta_l ..) (.conj (gs_index_delta_l ..) (gs_parity_delta_l ..))

theorem gs_base_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω B T E V : Term d) :
    Formula.satisfies ρ (gs_base_m ω B T E V) ↔ Gs_base_d (ω.eval ρ) (B.eval ρ) (T.eval ρ) (E.eval ρ) (V.eval ρ) := by
  simp only [gs_base_m,Gs_base_d,Formula.satisfies_conj_iff,gs_space_sat_l hE,gs_index_sat_l hE,gs_parity_sat_l hE]

theorem gs_base_iff_l (hZF : M.Models ZF) {ω B T E V : M.Domain} (space : Baire_d (kp_pair_l (ZF.modelsKP hZF)) ω B) :
    Gs_base_d ω B T E V ↔ Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T ∧
      M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) E T ω ∧
      ∀ n, M.mem n ω → (M.mem n V ↔ Gm_even_d (kp_pair_l (ZF.modelsKP hZF)) ω n) :=
  and_congr (gs_space_iff_l hZF space) (and_congr (gs_index_iff_l (ZF.modelsKP hZF)) (gs_parity_iff_l hZF space.1))

end YesMetaZFC.SetTheory.Descriptive

/-! ## 只量化实数及有限局面的有界决定性公式

给定实际局面编号和偶数集合，服从条件只检查有界函数图、前缀包含和
实数坐标。每个策略都有实数编码，且每个实数都解码为完整策略，因而
有界公式与原 Det_d 等价。公式本身为 Δ₀，不依赖见证集合满足集合论。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def gs_turn_m {d} (p : Bool) (V n : Term d) : Formula 1 d :=
  if p then .mem n V else .neg (.mem n V)

@[simp] theorem gs_turn_closed_l {d} (p : Bool) (V n : Term d)
    (hv : V.freeSupport = []) (hn : n.freeSupport = []) : (gs_turn_m p V n).FreeClosed := by
  cases p <;> exact ⟨hn,hv⟩

theorem gs_turn_delta_l {d} (p : Bool) (V n : Term d) : (gs_turn_m p V n).IsDelta0 := by
  cases p
  · exact .neg (.mem _ _)
  · exact .mem _ _

theorem gs_turn_sat_l {d} (ρ : Env M d) (p : Bool) (V n : Term d) :
    Formula.satisfies ρ (gs_turn_m p V n) ↔
      if p then M.mem (n.eval ρ) (V.eval ρ) else ¬ M.mem (n.eval ρ) (V.eval ρ) := by
  cases p <;> rfl

def Gs_follows_d (p : Bool) (ω T E V r x : M.Domain) : Prop :=
  ∀ n, M.mem n ω → (if p then M.mem n V else ¬ M.mem n V) →
    ∀ s, M.mem s T → Fn0_d n ω s → M.MemberSubset s x →
      ∀ a, M.mem a ω → Rd_entry_d n a x →
        ∃ i, M.mem i ω ∧ Rd_entry_d s i E ∧ Rd_entry_d i a r

def gs_follows_m {d} (p : Bool) (ω T E V r x : Term d) : Formula 1 d := set[d] ⟪
  ∀ n ∈ ⌜ω⌝ₛ, ⌜(gs_turn_m p)⌝ₚ(⌜V⌝ₛ,n) →
    (∀ s ∈ ⌜T⌝ₛ, ⌜fn0_m⌝ₚ(n,⌜ω⌝ₛ,s) → ⌜Formula.subset⌝ₚ(s,⌜x⌝ₛ) →
      (∀ a ∈ ⌜ω⌝ₛ, ⌜rd_entry0_m⌝ₚ(n,a,⌜x⌝ₛ) →
        (∃ i ∈ ⌜ω⌝ₛ, ⌜rd_entry0_m⌝ₚ(s,i,⌜E⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(i,a,⌜r⌝ₛ))))⟫

@[simp] theorem gs_follows_closed_l {d} (p : Bool) (ω T E V r x : Term d)
    (hw : ω.freeSupport = []) (ht : T.freeSupport = []) (he : E.freeSupport = [])
    (hv : V.freeSupport = []) (hr : r.freeSupport = []) (hx : x.freeSupport = []) :
    (gs_follows_m p ω T E V r x).FreeClosed := by
  simp -implicitDefEqProofs [gs_follows_m,Definitional.Formula.FreeClosed,hw,ht,he,hv,hr,hx]

theorem gs_follows_delta_l {d} (p : Bool) (ω T E V r x : Term d) :
    (gs_follows_m p ω T E V r x).IsDelta0 :=
  .forallMem _ (.imp (gs_turn_delta_l ..) (.forallMem _ (.imp (fn0_delta_l ..)
    (.imp (.atom _ _ _) (.forallMem _ (.imp (rd_entry0_delta_l ..)
      (.existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)))))))))

theorem gs_follows_sat_l (hE : Extensional M) {d} (ρ : Env M d) (p : Bool) (ω T E V r x : Term d) :
    Formula.satisfies ρ (gs_follows_m p ω T E V r x) ↔
      Gs_follows_d p (ω.eval ρ) (T.eval ρ) (E.eval ρ) (V.eval ρ) (r.eval ρ) (x.eval ρ) := by
  simp only [gs_follows_m,Gs_follows_d,Formula.satisfies_forallMem_iff,Formula.satisfies_imp_iff,
    gs_turn_sat_l,fn0_sat_l hE,Formula.satisfies_subset_iff,rd_entry0_sat_l hE,
    Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,Definitional.Term.eval_weaken]
  rfl

theorem gs_follows_iff_l (hKP : M.Models KP) {ω T E V r σ x : M.Domain} (p : Bool)
    (hw : M.IsOmega ω) (space : Fseq_space_d (kp_pair_l hKP) ω ω T)
    (index : M.IsSetFunctionFromTo (kp_pair_l hKP) E T ω)
    (parity : ∀ n, M.mem n ω → (M.mem n V ↔ Gm_even_d (kp_pair_l hKP) ω n))
    (decode : Gs_decode_d (kp_pair_l hKP) ω T E r σ) (real : M.IsSetFunctionFromTo (kp_pair_l hKP) x ω ω) :
    Gs_follows_d p ω T E V r x ↔ Gm_follows_d (kp_pair_l hKP) p ω σ x := by
  have turn n (hn : M.mem n ω) : Gm_turn_d (kp_pair_l hKP) p ω n ↔
      (if p then M.mem n V else ¬ M.mem n V) := by
    cases p
    · exact not_congr (parity n hn).symm
    · exact (parity n hn).symm
  constructor
  · intro h n hn play s cut a edge
    have fs := cut.isSetFunctionFromTo real (hw.transitive hKP n hn)
    have hs := (space s).mpr ⟨n,hn,fs⟩
    obtain ⟨i,_,si,ia⟩ := h n hn ((turn n hn).mp play) s hs (fn0_of_function_l hKP fs)
      ((ds_restrict_iff_l (kp_pair_l hKP) fs real.1).mp cut) a (real.output_mem_of_pairMember edge) edge
    exact (decode.2 s a hs).mp ⟨i,si,ia⟩
  · intro h n hn play s hs fs sub a _ edge
    have cut := (ds_restrict_iff_l (kp_pair_l hKP) (fn0_function_l hKP fs) real.1).mpr sub
    obtain ⟨i,si,ia⟩ := (decode.2 s a hs).mpr (h n hn ((turn n hn).mpr play) s cut a edge)
    exact ⟨i,index.output_mem_of_pairMember si,si,ia⟩

def Gs_win_d (p : Bool) (ω B T E V A r : M.Domain) : Prop :=
  ∀ x, M.mem x B → Gs_follows_d p ω T E V r x → if p then M.mem x A else ¬ M.mem x A

def gs_win_m {d} (p : Bool) (ω B T E V A r : Term d) : Formula 1 d := Formula.forallMem B
  (.imp (gs_follows_m p ω.weaken T.weaken E.weaken V.weaken r.weaken .newest)
    (if p then .mem .newest A.weaken else .neg (.mem .newest A.weaken)))

@[simp] theorem gs_win_closed_l {d} (p : Bool) (ω B T E V A r : Term d)
    (hw : ω.freeSupport = []) (hb : B.freeSupport = []) (ht : T.freeSupport = [])
    (he : E.freeSupport = []) (hv : V.freeSupport = []) (ha : A.freeSupport = []) (hr : r.freeSupport = []) :
    (gs_win_m p ω B T E V A r).FreeClosed := by
  cases p <;> simp -implicitDefEqProofs [gs_win_m,Definitional.Formula.FreeClosed,hw,hb,ht,he,hv,ha,hr]

theorem gs_win_delta_l {d} (p : Bool) (ω B T E V A r : Term d) : (gs_win_m p ω B T E V A r).IsDelta0 := by
  cases p
  · exact .forallMem _ (.imp (gs_follows_delta_l ..) (.neg (.mem _ _)))
  · exact .forallMem _ (.imp (gs_follows_delta_l ..) (.mem _ _))

theorem gs_win_sat_l (hE : Extensional M) {d} (ρ : Env M d) (p : Bool) (ω B T E V A r : Term d) :
    Formula.satisfies ρ (gs_win_m p ω B T E V A r) ↔
      Gs_win_d p (ω.eval ρ) (B.eval ρ) (T.eval ρ) (E.eval ρ) (V.eval ρ) (A.eval ρ) (r.eval ρ) := by
  cases p <;> simp only [gs_win_m,Gs_win_d,Bool.false_eq_true,↓reduceIte,Formula.satisfies_forallMem_iff,Formula.satisfies_imp_iff,
    gs_follows_sat_l hE,Formula.satisfies_mem_iff,Formula.satisfies_neg_iff,Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest]

def Gs_det_d (ω B T E V A : M.Domain) : Prop :=
  (∃ r, M.mem r B ∧ Gs_win_d true ω B T E V A r) ∨ ∃ r, M.mem r B ∧ Gs_win_d false ω B T E V A r

def gs_det_m {d} (ω B T E V A : Term d) : Formula 1 d :=
  .disj (Formula.existsMem B (gs_win_m true ω.weaken B.weaken T.weaken E.weaken V.weaken A.weaken .newest))
    (Formula.existsMem B (gs_win_m false ω.weaken B.weaken T.weaken E.weaken V.weaken A.weaken .newest))
derive_free_closed gs_det_m

theorem gs_det_delta_l {d} (ω B T E V A : Term d) : (gs_det_m ω B T E V A).IsDelta0 :=
  .disj (.existsMem _ (gs_win_delta_l ..)) (.existsMem _ (gs_win_delta_l ..))

theorem gs_det_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω B T E V A : Term d) :
    Formula.satisfies ρ (gs_det_m ω B T E V A) ↔
      Gs_det_d (ω.eval ρ) (B.eval ρ) (T.eval ρ) (E.eval ρ) (V.eval ρ) (A.eval ρ) := by
  simp only [gs_det_m,Gs_det_d,Formula.satisfies_disj_iff,Formula.satisfies_existsMem_iff,
    gs_win_sat_l hE,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

theorem gs_det_iff_l (hZF : M.Models ZF) {ω B T E V A : M.Domain}
    (space : Baire_d (kp_pair_l (ZF.modelsKP hZF)) ω B)
    (finite : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T)
    (index : M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) E T ω)
    (parity : ∀ n, M.mem n ω → (M.mem n V ↔ Gm_even_d (kp_pair_l (ZF.modelsKP hZF)) ω n)) :
    Det_d (kp_pair_l (ZF.modelsKP hZF)) ω B T A ↔ Gs_det_d ω B T E V A := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have win p : (∃ σ, Gm_win_d I p ω B T A σ) ↔ ∃ r, M.mem r B ∧ Gs_win_d p ω B T E V A r := by
    constructor
    · rintro ⟨σ,fn,all⟩
      obtain ⟨r,real,decode⟩ := gs_encode_l I hZF space index fn
      exact ⟨r,real,fun x hx follows => all x hx
        ((gs_follows_iff_l (ZF.modelsKP hZF) p space.1 finite index.1 parity decode ((space.2 x).mp hx)).mp follows)⟩
    · rintro ⟨r,real,all⟩
      obtain ⟨σ,decode⟩ := gs_decode_l I hZF index.1 ((space.2 r).mp real)
      exact ⟨σ,decode.1,fun x hx follows => all x hx
        ((gs_follows_iff_l (ZF.modelsKP hZF) p space.1 finite index.1 parity decode ((space.2 x).mp hx)).mpr follows)⟩
  exact or_congr (win true) (win false)

end YesMetaZFC.SetTheory.Descriptive

/-! ## 传递见证集合中准确核验决定性及非决定性

策略实数编码先将原决定性化为 Δ₀。任意包含原六项数据的传递集合
便准确判断此公式；证据来自实际完整 Baire 空间及编号，不给见证添加 ZF。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem gs_witness_l {ω B T : M.Domain} (space : Baire_d I ω B) (finite : Fseq_space_d I ω ω T) :
    ∃ E V, M.IsSetInjectionFromTo I E T ω ∧ M.MemberSubset V ω ∧
      (∀ n, M.mem n ω → (M.mem n V ↔ Gm_even_d I ω n)) ∧
      ∀ A Q, M.TransitiveSet Q → (∀ x ∈ [ω,B,T,E,V,A], M.mem x Q) →
        (St_d Q (gs_det_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5))
          (fun i => [ω,B,T,E,V,A].get i) ↔ Det_d I ω B T A) := by
  obtain ⟨E,V,number,sub,parity⟩ := gs_setup_l I hZF space.1 finite
  have index := number.function
  refine ⟨E,V,index,sub,parity,fun A Q trans inside => ?_⟩
  let ρ : Env M 6 := ⟨fun i => [ω,B,T,E,V,A].get i,fun _ => ω⟩
  let φ := gs_det_m (.bound 0 : Term 6) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5)
  have hc : φ.FreeClosed := gs_det_m_freeClosed _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
  have hd : φ.IsDelta0 := gs_det_delta_l ..
  have params i : M.mem (ρ.bound i) Q := inside _ (List.get_mem ..)
  exact (st_delta_l trans ⟨ω,inside ω (by simp)⟩ φ hc hd ρ params).trans
    ((gs_det_sat_l hZF.1 ρ _ _ _ _ _ _).trans (gs_det_iff_l hZF space finite index parity).symm)

end YesMetaZFC.SetTheory.Descriptive
