import YesMetaZFC.SetTheory.LargeCardinal.Game.Round
import YesMetaZFC.Model.SetTheory.Internal.MembershipSlice
import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNameSyntax
import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding
import YesMetaZFC.Model.SetTheory.Relations.RecordImage
import YesMetaZFC.Model.SetTheory.Relations.Parity

/-! # 历轮回答的完整原模型记录

记录先保存 ω 和共同秩段，再保存原轮的五十四个坐标。域、常量域、查询域
和完整回答都属于该共同层；原实现、弹性和任意排列证书仍在原反射层内。
秩、成员关系及闭包均按原关系解释；原更新输入还保留标签图的自然数值域。
历史行另存后续树步实际使用的源证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_saved_record0_m : Formula 1 56 := .conj
  (tg_round0_m.rename (fun i => i.succ.succ))
  (set[56] ⟪⌜(.bound 18 : Term 56)⌝ₛ = ⌜(.bound 0 : Term 56)⌝ₛ ∧
    ⌜(.bound 17 : Term 56)⌝ₛ ∈ ⌜(.bound 1 : Term 56)⌝ₛ ∧
    ⌜(.bound 15 : Term 56)⌝ₛ ∈ ⌜(.bound 1 : Term 56)⌝ₛ ∧
    ⌜(.bound 14 : Term 56)⌝ₛ ∈ ⌜(.bound 1 : Term 56)⌝ₛ ∧
    ⌜(.bound 13 : Term 56)⌝ₛ ∈ ⌜(.bound 1 : Term 56)⌝ₛ⟫)

theorem tg_saved_record0_closed_l : tg_saved_record0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_saved_record0_m, Definitional.Formula.FreeClosed, tg_round0_closed_l]

structure Tg_saved_d (I : kpair_convention_l.Interpretation M) (ω Y R η C L V q : M.Domain) : Prop where
  ext : Rf_ext_d I Y R
  context : Tg_context_d I ω Y R η C
  limit : Rr_truth_d (n := 0) I Y R (Formula.isLimitOrdinal .newest) (fun _ => L)
  member : M.PairMember I V C R
  rank : Rr_truth_d (n := 1) I Y R (v_sigma_m (.bound 1) .newest) (Fin.cases V (fun _ => L))
  record : Rf_record_d I Y R tg_saved_record0_m C q
  head : ∃ r, Rf_tuple_d (n := 2) I Y R (Fin.cases ω (Fin.cases V (fun _ => r))) q

def tg_saved_m {d} (ω Y R η C L V q : Term d) : Formula 1 d := .conj
  (rf_ext_m (𝒞 := kpair_convention_l) Y R) (.conj (tg_context_data_m ω Y R η C) (.conj
  (rr_truth_m (𝒞 := kpair_convention_l) (n := 0) (Formula.isLimitOrdinal .newest) Y R (fun _ => L)) (.conj
  (Formula.orderedPairMem kpair_convention_l V C R) (.conj
  (rr_truth_m (𝒞 := kpair_convention_l) (n := 1) (v_sigma_m (.bound 1) .newest) Y R (Fin.cases V (fun _ => L))) (.conj
  (rf_record_m (𝒞 := kpair_convention_l) tg_saved_record0_m Y R C q)
  (set[d] ⟪∃ r, ⌜fun Y R ω V r q => rf_tuple_m (𝒞 := kpair_convention_l) (n := 2) Y R
    (Fin.cases ω (Fin.cases V (fun _ => r))) q⌝ₚ(⌜Y⌝ₛ, ⌜R⌝ₛ, ⌜ω⌝ₛ, ⌜V⌝ₛ, r, ⌜q⌝ₛ)⟫))))))

@[simp] theorem tg_saved_closed_l {d} (ω Y R η C L V q : Term d)
    (hw : ω.freeSupport = []) (hY : Y.freeSupport = []) (hR : R.freeSupport = [])
    (hη : η.freeSupport = []) (hC : C.freeSupport = []) (hL : L.freeSupport = [])
    (hV : V.freeSupport = []) (hq : q.freeSupport = []) : (tg_saved_m ω Y R η C L V q).FreeClosed := by
  simp only [tg_saved_m, Definitional.Formula.FreeClosed]
  refine ⟨by simp -implicitDefEqProofs [hY, hR] , tg_context_data_closed_l _ _ _ _ _ hw hY hR hη hC,
    rr_truth_closed_l _ (by simp -implicitDefEqProofs) _ _ _ hY hR (fun _ => hL),
    by simp -implicitDefEqProofs [hV, hC, hR] ,
    rr_truth_closed_l _ (by simp -implicitDefEqProofs) _ _ _ hY hR (Fin.cases hV (fun _ => hL)),
    rf_record_closed_l _ tg_saved_record0_closed_l _ _ _ _ hY hR hC hq, ?_⟩
  exact rf_tuple_closed_l (n := 2) Y.weaken R.weaken
    (Fin.cases ω.weaken (Fin.cases V.weaken (fun _ => .newest))) q.weaken
    (by simpa using hY) (by simpa using hR)
    (Fin.cases (by simpa using hw)
      (Fin.cases (by change V.weaken.freeSupport = []; simpa using hV) (fun _ => rfl))) (by simpa using hq)

section Native
variable (I : kpair_convention_l.Interpretation M)

theorem tg_saved_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω Y R η C L V q : Term d) :
    Formula.satisfies ρ (tg_saved_m ω Y R η C L V q) ↔
      Tg_saved_d I (ω.eval ρ) (Y.eval ρ) (R.eval ρ) (η.eval ρ) (C.eval ρ) (L.eval ρ) (V.eval ρ) (q.eval ρ) := by
  simp only [tg_saved_m, Formula.satisfies_conj_iff, rf_ext_sat_l I hE, tg_context_data_sat_l I,
    rr_truth_sat_l I ρ (Formula.isLimitOrdinal (.newest : Term 1)) (by simp -implicitDefEqProofs),
    rr_truth_sat_l I ρ (v_sigma_m (.bound 1) (.newest : Term 2)) (by simp -implicitDefEqProofs),
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_exists_iff,
    rf_tuple_sat_l I, rf_record_sat_l I _ _ tg_saved_record0_closed_l, Definitional.Term.eval_weaken]
  have row : (fun i : Fin 2 => ((Fin.cases V (fun _ => L) : Fin 2 → Term d) i).eval ρ) =
      Fin.cases (V.eval ρ) (fun _ => L.eval ρ) := funext (Fin.cases rfl (fun _ => rfl))
  have head (r : M.Domain) :
      (fun i : Fin 3 => ((Fin.cases ω.weaken (Fin.cases V.weaken (fun _ => .newest)) :
        Fin 3 → Term (d+1)) i).eval (ρ.push r)) =
      Fin.cases (ω.eval ρ) (Fin.cases (V.eval ρ) (fun _ => r)) :=
    funext (Fin.cases (Definitional.Term.eval_weaken ρ r ω)
      (Fin.cases (Definitional.Term.eval_weaken ρ r V) (fun _ => rfl)))
  simp only [row, head]
  exact ⟨fun ⟨e, c, l, m, v, r, a⟩ => ⟨e, c, l, m, v, r, a⟩,
    fun h => ⟨h.ext, h.context, h.limit, h.member, h.rank, h.record, h.head⟩⟩

/-- 原反射层中恢复完整回答；源模型无需外部传递或可数闭包。 -/
theorem Tg_saved_d.read_l (hE : Extensional M) {ω Y R η C L V q : M.Domain}
    (h : Tg_saved_d I ω Y R η C L V q) :
    let N₀ := smdl_structure_l I (R := R) ⟨ω, h.context.omega_mem⟩
    let C₀ : N₀.Domain := ⟨C, h.context.member⟩
    ∃ nc : Nonempty {x : N₀.Domain // N₀.mem x C₀},
      ∃ ρ : Env (rt_model_l C₀ nc) 54,
        Tg_saved_code_d Y R ω V q (fun i => (ρ.bound i).val.val) ∧
        Formula.satisfies ρ tg_round0_m ∧ (ρ.bound 16).val.val = ω ∧
        M.PairMember I (ρ.bound 15).val.val V R ∧ M.PairMember I (ρ.bound 13).val.val V R ∧
        M.PairMember I (ρ.bound 12).val.val V R ∧ M.PairMember I (ρ.bound 11).val.val V R := by
  let nx : ∃ x, M.mem x Y := ⟨ω, h.context.omega_mem⟩
  let N₀ := smdl_structure_l I (R := R) nx
  let C₀ : N₀.Domain := ⟨C, h.context.member⟩
  let q₀ : N₀.Domain := ⟨q, h.record.elim fun mem _ => mem 1⟩
  have en := h.ext.native_l I nx
  have fs := h.context.finite_l nx en
  let nc : Nonempty {x : N₀.Domain // N₀.mem x C₀} := ⟨⟨⟨ω, h.context.omega_mem⟩, fs.omega_mem⟩⟩
  obtain ⟨_, σ, tuple, valid⟩ :=
    (rf_record_read_l I nx en tg_saved_record0_m tg_saved_record0_closed_l C₀ q₀ fs.transitive nc).mp h.record
  obtain ⟨s, hs, t, ht, _⟩ := (rf_tuple_native_l I nx en (fun i => (σ.bound i).val) q₀).mp tuple
  obtain ⟨r, head⟩ := h.head
  have members := head.elim fun mem _ => mem
  let v : Fin 3 → N₀.Domain := fun i =>
    ⟨(Fin.cases ω (Fin.cases V (fun _ => r)) : Fin 3 → M.Domain) i, members i.succ⟩
  obtain ⟨a, ha, b, hb, _⟩ := (rf_tuple_native_l I nx en v q₀).mp head
  obtain ⟨hw, eq⟩ := kpair_injective_l N₀ hs ha
  have hV := (kpair_injective_l N₀ ht (eq.symm ▸ hb)).1
  have hw : (σ.bound 0).val.val = ω := congrArg (fun x : N₀.Domain => x.val) hw
  have hV : (σ.bound 1).val.val = V := congrArg (fun x : N₀.Domain => x.val) hV
  obtain ⟨round, links⟩ := (Formula.satisfies_conj_iff ..).mp valid
  let ρ : Env (rt_model_l C₀ nc) 54 :=
    ⟨fun i => σ.bound i.succ.succ, fun _ => σ.bound 0⟩
  have round : Formula.satisfies ρ tg_round0_m :=
    (Formula.closed_env_l tg_round0_m tg_round0_closed_l
      (ρ := σ.reindex (fun i : Fin 54 => i.succ.succ)) (η := ρ) rfl).mp ((Formula.satisfies_rename ..).mp round)
  simp only [Formula.satisfies_conj_iff, Formula.satisfies_extensionalEq_iff_eq (rt_model_ext_l en fs.transitive nc),
    Formula.satisfies_mem_iff] at links
  have row : (fun i : Fin 56 => (σ.bound i).val.val) =
      Fin.cases ω (Fin.cases V (fun i => (ρ.bound i).val.val)) :=
    funext (Fin.cases hw (Fin.cases hV (fun _ => rfl)))
  have shift x (hx : M.PairMember I x (σ.bound 1).val.val R) : M.PairMember I x V R :=
    Eq.mp (congrArg (fun a => M.PairMember I x a R) hV) hx
  exact ⟨nc, ρ, (tg_saved_code_read_l I hE).mpr ⟨h.ext, row ▸ tuple⟩, round,
    (congrArg (fun x : (rt_model_l C₀ nc).Domain => x.val.val) links.1).trans hw,
    shift _ links.2.1, shift _ links.2.2.1, shift _ links.2.2.2.1, shift _ links.2.2.2.2⟩

/-- 真正的隶属切片按同一坐标读取；记录码仍保留原关系解释。 -/
theorem Tg_saved_d.membership_l (hE : Extensional M) {ω Y R η C L V q c : M.Domain}
    (h : Tg_saved_d I ω Y R η C L V q) (model : Smem_d I c Y R) (inside : M.MemberSubset C Y)
    (nc : Nonempty {x // M.mem x C}) :
    ∃ ρ : Env (rt_model_l C nc) 54, Tg_saved_code_d Y R ω V q (fun i => (ρ.bound i).val) ∧
      Formula.satisfies ρ tg_round0_m ∧ (ρ.bound 16).val = ω ∧
      M.mem (ρ.bound 15).val V ∧ M.mem (ρ.bound 13).val V ∧
      M.mem (ρ.bound 12).val V ∧ M.mem (ρ.bound 11).val V := by
  obtain ⟨nd, σ, code, valid, hw, hτ, hU, hD, hv⟩ := h.read_l I hE
  let C₀ : (smdl_structure_l I (R := R) model.1.2.1).Domain := ⟨C, h.context.member⟩
  let ρ := model.slice_env_d I C₀ nd nc σ
  exact ⟨ρ, code, (model.slice_formula_l I C₀ inside nd nc tg_round0_m σ).mp valid, hw,
    ((model.2 _ V).mp hτ).2.2, ((model.2 _ V).mp hU).2.2,
    ((model.2 _ V).mp hD).2.2, ((model.2 _ V).mp hv).2.2⟩

/-- 原回答直接存入自己的原反射层，仅用外延性和该层的配对闭包。 -/
theorem Tg_context_d.save_l (hE : Extensional M) {ω Y R η C L V : M.Domain}
    (context : Tg_context_d I ω Y R η C) (ext : Rf_ext_d I Y R)
    (limit : Rr_truth_d (n := 0) I Y R (Formula.isLimitOrdinal .newest) (fun _ => L))
    (rank : Rr_truth_d (n := 1) I Y R (v_sigma_m (.bound 1) .newest) (Fin.cases V (fun _ => L)))
    (member : M.PairMember I V C R)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) ⟨ω, context.omega_mem⟩).Domain //
      (smdl_structure_l I (R := R) ⟨ω, context.omega_mem⟩).mem x ⟨C, context.member⟩})
    (ρ : Env (rt_model_l (M := smdl_structure_l I (R := R) ⟨ω, context.omega_mem⟩) ⟨C, context.member⟩ nc) 54)
    (valid : Formula.satisfies ρ tg_round0_m) (hw : (ρ.bound 16).val.val = ω)
    (low : M.PairMember I (ρ.bound 15).val.val V R ∧ M.PairMember I (ρ.bound 13).val.val V R ∧
      M.PairMember I (ρ.bound 12).val.val V R ∧ M.PairMember I (ρ.bound 11).val.val V R) :
    ∃ q, Tg_saved_d I ω Y R η C L V q ∧ Tg_saved_code_d Y R ω V q (fun i => (ρ.bound i).val.val) := by
  let nx : ∃ x, M.mem x Y := ⟨ω, context.omega_mem⟩
  let N₀ := smdl_structure_l I (R := R) nx
  let C₀ : N₀.Domain := ⟨C, context.member⟩
  have en := ext.native_l I nx
  have fs := context.finite_l nx en
  let w : N₀.Domain := ⟨ω, context.omega_mem⟩
  let V₀ : N₀.Domain := ⟨V, rank.elim fun m _ => m 0⟩
  let v : Fin 56 → (rt_model_l C₀ nc).Domain := Fin.cases ⟨w, fs.omega_mem⟩ (Fin.cases ⟨V₀, member⟩ ρ.bound)
  let ε : Env (rt_model_l C₀ nc) 56 := ⟨v, fun _ => v 0⟩
  have original : Formula.satisfies (ε.reindex (fun i : Fin 54 => i.succ.succ)) tg_round0_m :=
    (Formula.closed_env_l tg_round0_m tg_round0_closed_l (ρ := ε.reindex (fun i : Fin 54 => i.succ.succ)) (η := ρ) rfl).mpr valid
  have valid : Formula.satisfies ε tg_saved_record0_m := by
    apply (Formula.satisfies_conj_iff ..).mpr
    refine ⟨(Formula.satisfies_rename ε (fun i : Fin 54 => i.succ.succ) tg_round0_m).mpr original, ?_⟩
    simp only [Formula.satisfies_conj_iff, Formula.satisfies_extensionalEq_iff_eq (rt_model_ext_l en fs.transitive nc),
      Formula.satisfies_mem_iff]
    exact ⟨Subtype.ext (Subtype.ext hw), low⟩
  obtain ⟨q, record, values⟩ := rf_record_save_l I nx en tg_saved_record0_m tg_saved_record0_closed_l
    C₀ fs.transitive fs.pair nc ε valid
  have head : ∃ r, Rf_tuple_d (n := 2) I Y R (Fin.cases ω (Fin.cases V (fun _ => r))) q.val := by
    obtain ⟨s, hs, r, hr, _⟩ := (rf_tuple_native_l I nx en (fun i => (ε.bound i).val) q).mp values
    let t : Fin 3 → N₀.Domain := Fin.cases w (Fin.cases V₀ (fun _ => r))
    have saved := (rf_tuple_native_l I nx en t q).mpr ⟨s, hs, r, hr, rfl⟩
    have eq : (fun i => (t i).val) = (Fin.cases ω (Fin.cases V (fun _ => r.val)) : Fin 3 → M.Domain) :=
      funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
    exact ⟨r.val, eq ▸ saved⟩
  have row : (fun i : Fin 56 => (ε.bound i).val.val) =
      Fin.cases ω (Fin.cases V (fun i => (ρ.bound i).val.val)) := funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
  exact ⟨q.val, ⟨ext, context, limit, member, rank, record, head⟩,
    (tg_saved_code_read_l I hE).mpr ⟨ext, row ▸ values⟩⟩

theorem Tg_saved_d.member_l {ω Y R η C L V q c : M.Domain}
    (h : Tg_saved_d I ω Y R η C L V q) (model : Smem_d I c Y R) : M.mem V C :=
  ((model.2 V C).mp h.member).2.2

theorem Tg_saved_d.rank_l (hKP : M.Models KP) {ω Y R η C L V q c : M.Domain}
    (h : Tg_saved_d I ω Y R η C L V q) (trans : M.TransitiveSet Y) (model : Smem_d I c Y R) : Vr_d Y L V := by
  obtain ⟨m, valid⟩ := h.rank
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨V, m 0⟩⟩
  let ρ : Env (rt_model_l Y ny) 2 :=
    ⟨fun i => ⟨(Fin.cases V (fun _ => L) : Fin 2 → M.Domain) i, m i⟩, fun _ => ⟨V, m 0⟩⟩
  exact (vr_sat_l hKP trans ny ρ (.bound 1) .newest).mp ((smem_formula_l I model ny _ ρ).mpr valid)

theorem Tg_saved_d.limit_l (hKP : M.Models KP) {ω Y R η C L V q c : M.Domain}
    (h : Tg_saved_d I ω Y R η C L V q) (trans : M.TransitiveSet Y) (model : Smem_d I c Y R) : M.IsLimitOrdinal L := by
  obtain ⟨m, valid⟩ := h.limit
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨L, m 0⟩⟩
  let a : (rt_model_l Y ny).Domain := ⟨L, m 0⟩
  have truth := (smem_formula_l I model ny _ (⟨fun _ => a, fun _ => a⟩ : Env (rt_model_l Y ny) 1)).mpr valid
  exact (rt_limit_l trans ny hKP a).mp ((Formula.satisfies_isLimitOrdinal_iff ..).mp truth)

end Native

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 实际回答的三个低坐标由原语言回收，再调用同一原关系保存接口。 -/
theorem Tg_context_d.save_round_l {ω Y R μ K η C L V : M.Domain}
    (context : Tg_context_d I ω Y R η C) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K Y R)
    (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 54)
    (valid : Formula.satisfies ρ tg_round0_m) (hw : (ρ.bound 16).val = ω)
    (limit : M.IsLimitOrdinal L) (member : M.mem V C) (rank : Vr_d Y L V)
    (below : M.mem (ρ.bound 15).val L) (answer : M.mem (ρ.bound 11).val V) :
    ∃ q, Tg_saved_d I ω Y R η C L V q ∧ Tg_saved_code_d Y R ω V q (fun i => (ρ.bound i).val) := by
  have hV := source.transitive C context.member V member
  have hτ := rank.ordinal_subset_l hZF source.transitive hV _ below
  have body := (Formula.satisfies_conj_iff ..).mp valid |>.2
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff] at body
  have language := body.2.2.2.2.2.2.1
  let f : Fin 10 → Term 54 := fun i => [.bound 16, .bound 15, .bound 24, .bound 14, .bound 13,
    .bound 12, .bound 6, .bound 5, .bound 4, .bound 3].get i
  let ε := Definitional.Env.substitute ρ f
  have language : Formula.satisfies ε ee_language0_m := (Formula.satisfies_bind ρ f ee_language0_m).mp language
  have facts := language
  simp only [ee_language0_m, Formula.satisfies_conj_iff] at facts
  have fs := (context.read_l hZF source).1
  have hκ := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) (ρ.bound 15)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp facts.2.1)
  have hω := rank.subset_mem_l source.transitive hV hτ source.omega_mem
    (source.omega.subset_limitOrdinal (ZF.modelsKP hZF) hκ)
  obtain ⟨_, _, low, _⟩ := context.language_rank_l hZF nc ε source hV rank limit hω hτ hw language
  obtain ⟨c, model⟩ := source.code
  have data := rank
  obtain ⟨B, F, _, hF, history⟩ := data
  have hL := sc_function_domain_mem_l hZF source.omega source.transitive model source.theory hF (history V hV).2.1
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨ω, source.omega_mem⟩⟩
  let a : (rt_model_l Y ny).Domain := ⟨L, hL⟩
  let v : Fin 2 → (rt_model_l Y ny).Domain := fun i =>
    ⟨(Fin.cases V (fun _ => L) : Fin 2 → M.Domain) i, Fin.cases hV (fun _ => hL) i⟩
  have rank' : Rr_truth_d (n := 1) I Y R (v_sigma_m (.bound 1) .newest) (Fin.cases V (fun _ => L)) :=
    ⟨Fin.cases hV (fun _ => hL), (smem_formula_l I model ny _ (⟨v, fun _ => v 0⟩ : Env (rt_model_l Y ny) 2)).mp
      ((vr_sat_l (ZF.modelsKP hZF) source.transitive ny _ (.bound 1) .newest).mpr rank)⟩
  have limit' : Rr_truth_d (n := 0) I Y R (Formula.isLimitOrdinal .newest) (fun _ => L) :=
    ⟨fun _ => hL, (smem_formula_l I model ny _ (⟨fun _ => a, fun _ => a⟩ : Env (rt_model_l Y ny) 1)).mp
      ((Formula.satisfies_isLimitOrdinal_iff ..).mpr ((rt_limit_l source.transitive ny (ZF.modelsKP hZF) a).mpr limit))⟩
  let nx : ∃ x, M.mem x Y := ⟨ω, context.omega_mem⟩
  let N₀ := smdl_structure_l I (R := R) nx
  let C₀ : N₀.Domain := ⟨C, context.member⟩
  have ext := rf_ext_mem_l I hZF.1 source.transitive model
  have finite := context.finite_l nx (ext.native_l I nx)
  let nd : Nonempty {x : N₀.Domain // N₀.mem x C₀} := ⟨⟨⟨ω, context.omega_mem⟩, finite.omega_mem⟩⟩
  let σ := model.native_env_d I C₀ (source.transitive C context.member) nd nc ρ
  have lift x (hx : M.mem x V) := (model.2 x V).mpr ⟨source.transitive V hV x hx, hV, hx⟩
  exact context.save_l I hZF.1 ext limit' rank' ((model.2 V C).mpr ⟨hV, context.member, member⟩) nd σ
    ((model.native_formula_l I C₀ (source.transitive C context.member) nd nc tg_round0_m ρ).mp valid)
    hw ⟨lift _ hτ, lift _ (low 4), lift _ (low 5), lift _ answer⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 统一历史中的全部旧回答

历史是背景模型自己的序数长度函数图。每行记录原树结点、树步的工作源
证书、原关系存档及当前共同秩段；改变当前模型时，原行逐字保留。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_past_cell_d (r i Y R μ K η C L V q : M.Domain) : Prop :=
  Rt_tuple_d (fun j => [i, Y, R, μ, K, η, C, L, V, q].get j) r

def tg_past_cell_m {d} (r i Y R μ K η C L V q : Term d) : Formula 1 d :=
  rt_tuple_m (fun j => [i, Y, R, μ, K, η, C, L, V, q].get j) r

@[simp] theorem tg_past_cell_closed_l {d} (r i Y R μ K η C L V q : Term d)
    (hr : r.freeSupport = []) (hi : i.freeSupport = []) (hY : Y.freeSupport = []) (hR : R.freeSupport = [])
    (hμ : μ.freeSupport = []) (hK : K.freeSupport = []) (hη : η.freeSupport = [])
    (hC : C.freeSupport = []) (hL : L.freeSupport = []) (hV : V.freeSupport = []) (hq : q.freeSupport = []) :
    (tg_past_cell_m r i Y R μ K η C L V q).FreeClosed := by
  apply rt_tuple_closed_l _ _ ?_ hr
  intro j
  exact Fin.cases hi (Fin.cases hY (Fin.cases hR (Fin.cases hμ (Fin.cases hK
    (Fin.cases hη (Fin.cases hC (Fin.cases hL (Fin.cases hV (Fin.cases hq (fun k => Fin.elim0 k)))))))))) j

theorem tg_past_cell_sat_l (hE : Extensional M) {d} (ρ : Env M d) (r i Y R μ K η C L V q : Term d) :
    Formula.satisfies ρ (tg_past_cell_m r i Y R μ K η C L V q) ↔
      Tg_past_cell_d (r.eval ρ) (i.eval ρ) (Y.eval ρ) (R.eval ρ) (μ.eval ρ) (K.eval ρ)
        (η.eval ρ) (C.eval ρ) (L.eval ρ) (V.eval ρ) (q.eval ρ) := by
  rw [tg_past_cell_m, rt_tuple_sat_l hE]
  have eq : (fun j : Fin 10 => ([i, Y, R, μ, K, η, C, L, V, q].get j).eval ρ) =
      (fun j => [i.eval ρ, Y.eval ρ, R.eval ρ, μ.eval ρ, K.eval ρ, η.eval ρ, C.eval ρ, L.eval ρ, V.eval ρ, q.eval ρ].get j) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))))))) j
  exact eq ▸ Iff.rfl

def Tg_past_at_d (H n i Y R μ K η C L V q : M.Domain) : Prop :=
  ∃ r, Rd_entry_d n r H ∧ Tg_past_cell_d r i Y R μ K η C L V q

def tg_past_at_m {d} (H n i Y R μ K η C L V q : Term d) : Formula 1 d := set[d] ⟪
  ∃ r, ⌜rd_entry0_m⌝ₚ(⌜n⌝ₛ, r, ⌜H⌝ₛ) ∧
    ⌜tg_past_cell_m⌝ₚ(r, ⌜i⌝ₛ, ⌜Y⌝ₛ, ⌜R⌝ₛ, ⌜μ⌝ₛ, ⌜K⌝ₛ, ⌜η⌝ₛ, ⌜C⌝ₛ, ⌜L⌝ₛ, ⌜V⌝ₛ, ⌜q⌝ₛ)⟫
derive_free_closed tg_past_at_m

theorem tg_past_at_sat_l (hE : Extensional M) {d} (ρ : Env M d) (H n i Y R μ K η C L V q : Term d) :
    Formula.satisfies ρ (tg_past_at_m H n i Y R μ K η C L V q) ↔
      Tg_past_at_d (H.eval ρ) (n.eval ρ) (i.eval ρ) (Y.eval ρ) (R.eval ρ) (μ.eval ρ)
        (K.eval ρ) (η.eval ρ) (C.eval ρ) (L.eval ρ) (V.eval ρ) (q.eval ρ) := by
  simp only [tg_past_at_m, Tg_past_at_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE, tg_past_cell_sat_l hE, Definitional.Term.eval_weaken]
  rfl

def Tg_past_links_d (I : kpair_convention_l.Interpretation M) (H Q : M.Domain) : Prop :=
  ∀ m i Y R μ K η C L V q, Tg_past_at_d H m i Y R μ K η C L V q → ∃ c, Rd_entry_d i c Q ∧ Smem_d I c Y R

def tg_past_links_m {d} (H Q : Term d) : Formula 1 d := set[d] ⟪
  ∀ m i Y R μ K η C L V q, ⌜tg_past_at_m⌝ₚ(⌜H⌝ₛ, m, i, Y, R, μ, K, η, C, L, V, q) →
    ∃ c, ⌜rd_entry0_m⌝ₚ(i, c, ⌜Q⌝ₛ) ∧ ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, R)⟫
derive_free_closed tg_past_links_m

theorem tg_past_links_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (H Q : Term d) : Formula.satisfies ρ (tg_past_links_m H Q) ↔
      Tg_past_links_d I (H.eval ρ) (Q.eval ρ) := by
  simp only [tg_past_links_m, Tg_past_links_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, tg_past_at_sat_l hE,
    rd_entry0_sat_l hE, smem_sat_l I, Definitional.Term.eval_weaken]
  rfl

theorem tg_past_links_empty_l (I : kpair_convention_l.Interpretation M) {e Q : M.Domain}
    (he : ∀ x, ¬ M.mem x e) : Tg_past_links_d I e Q :=
  fun _ _ _ _ _ _ _ _ _ _ _ ⟨_, ⟨p, _, hp⟩, _⟩ => (he p hp).elim

def Tg_past_fixed_d (H j : M.Domain) : Prop := ∀ m i Y R μ K η C L V q,
  Tg_past_at_d H m i Y R μ K η C L V q → ∀ x, M.mem x V → Rd_entry_d x x j

structure Tg_past_d (hZF : M.Models ZF) (ω n H X b : M.Domain) : Prop where
  sequence : M.IsSequenceOfLength (kp_pair_l (ZF.modelsKP hZF)) H n
  rows : ∀ m r, Rd_entry_d m r H → ∃ i Y R μ K η C L V q,
    Tg_past_cell_d r i Y R μ K η C L V q ∧ Ic_model_d hZF ω μ K Y R ∧
      Tg_saved_d (kp_pair_l (ZF.modelsKP hZF)) ω Y R η C L V q ∧
    M.mem V X ∧ Vr_d X L V ∧ M.MemberSubset L b

def tg_past_m {d} (ω n H X b : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isOrdinal⌝ₚ(⌜n⌝ₛ) ∧ ⌜Formula.isFunction kpair_convention_l⌝ₚ(⌜H⌝ₛ) ∧
  ⌜Formula.isDomain kpair_convention_l⌝ₚ(⌜n⌝ₛ, ⌜H⌝ₛ) ∧
  (∀ m r, ⌜rd_entry0_m⌝ₚ(m, r, ⌜H⌝ₛ) → ∃ i Y R μ K η C L V q,
    ⌜tg_past_cell_m⌝ₚ(r, i, Y, R, μ, K, η, C, L, V, q) ∧
    ⌜ic_model_m⌝ₚ(⌜ω⌝ₛ, μ, K, Y, R) ∧ ⌜tg_saved_m⌝ₚ(⌜ω⌝ₛ, Y, R, η, C, L, V, q) ∧
    V ∈ ⌜X⌝ₛ ∧ ⌜pn_rank_m⌝ₚ(⌜X⌝ₛ, L, V) ∧ L ⊆ ⌜b⌝ₛ)⟫
derive_free_closed tg_past_m

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_past_sat_l {d} (ρ : Env M d) (ω n H X b : Term d) :
    Formula.satisfies ρ (tg_past_m ω n H X b) ↔
      Tg_past_d hZF (ω.eval ρ) (n.eval ρ) (H.eval ρ) (X.eval ρ) (b.eval ρ) := by
  simp only [tg_past_m, Formula.satisfies_conj_iff, Formula.satisfies_isOrdinal_iff,
    Formula.satisfies_isFunction_iff I hZF.1, Formula.satisfies_isDomain_iff I,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_exists_iff,
    rd_entry0_sat_l hZF.1, tg_past_cell_sat_l hZF.1, ic_model_sat_l hZF, tg_saved_sat_l I hZF.1,
    Formula.satisfies_mem_iff, pn_rank_sat_l (ZF.modelsKP hZF), Formula.satisfies_subset_iff,
    Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨⟨a, b, c⟩, d⟩,
    fun h => ⟨h.sequence.1, h.sequence.2.1, h.sequence.2.2, h.rows⟩⟩

theorem tg_past_empty_l {ω e X b : M.Domain} (he : ∀ x, ¬ M.mem x e) : Tg_past_d hZF ω e e X b := by
  have fn : Fn0_d e e e := ⟨fun p hp => (he p hp).elim, fun p hp => (he p hp).elim, fun p hp => (he p hp).elim⟩
  have graph := fn0_function_l (ZF.modelsKP hZF) fn
  exact ⟨⟨Structure.IsOrdinal.of_no_members he, graph.1, graph.2.1⟩,
    fun _ _ ⟨p, _, hp⟩ => (he p hp).elim⟩

/-- 指定轮号直接读回同一原模型、原证书与当前共同秩段。 -/
theorem Tg_past_d.read_l {ω n H X b m i Y R μ K η C L V q : M.Domain}
    (h : Tg_past_d hZF ω n H X b) (ha : Tg_past_at_d H m i Y R μ K η C L V q) :
    Ic_model_d hZF ω μ K Y R ∧ Tg_saved_d I ω Y R η C L V q ∧
      M.mem V X ∧ Vr_d X L V ∧ M.MemberSubset L b := by
  obtain ⟨r, hr, cell⟩ := ha
  obtain ⟨i', Y', R', μ', K', η', C', L', V', q', cell', source, saved, member, rank, bound⟩ := h.rows m r hr
  have eq := rt_tuple_inj_l cell' cell
  have eY : Y' = Y := congrFun eq 1; have eR : R' = R := congrFun eq 2
  have eμ : μ' = μ := congrFun eq 3; have eK : K' = K := congrFun eq 4; have eη : η' = η := congrFun eq 5
  have eC : C' = C := congrFun eq 6; have eL : L' = L := congrFun eq 7
  have eV : V' = V := congrFun eq 8; have eq' : q' = q := congrFun eq 9
  exact eY ▸ eR ▸ eμ ▸ eK ▸ eη ▸ eC ▸ eL ▸ eV ▸ eq' ▸ ⟨source, saved, member, rank, bound⟩

/-- 增加一行时，全部旧记录保持原值，且仍能按原轮号访问。 -/
theorem Tg_past_d.push_l {ω n H X b n' b' i Y R μ K η C L V q : M.Domain}
    (h : Tg_past_d hZF ω n H X b) (succ : M.SuccessorOf n' n)
    (source : Ic_model_d hZF ω μ K Y R) (saved : Tg_saved_d I ω Y R η C L V q) (member : M.mem V X) (rank : Vr_d X L V)
    (oldBound : M.MemberSubset b b') (bound : M.MemberSubset L b') :
    ∃ H', Tg_past_d hZF ω n' H' X b' ∧ Tg_past_at_d H' n i Y R μ K η C L V q ∧
      ∀ m r, M.mem m n → (Rd_entry_d m r H' ↔ Rd_entry_d m r H) := by
  obtain ⟨r, cell⟩ := rt_tuple_exists_l (ZF.modelsKP hZF) (fun j => [i, Y, R, μ, K, η, C, L, V, q].get j)
  obtain ⟨H', seq, entries⟩ := Structure.IsSequenceOfLength.exists_append (value := r) (ZF.modelsKP hZF) I
    h.sequence (KP.successor_isOrdinal (ZF.modelsKP hZF) h.sequence.1 succ) succ
  refine ⟨H', ⟨seq, ?_⟩, ⟨r, (entries n r).mpr (Or.inr ⟨rfl, rfl⟩), cell⟩, ?_⟩
  · intro m s hs
    rcases (entries m s).mp hs with hs | ⟨_, rfl⟩
    · obtain ⟨i, Y, R, μ, K, η, C, L, V, q, cell, source, saved, member, rank, bound⟩ := h.rows m s hs
      exact ⟨i, Y, R, μ, K, η, C, L, V, q, cell, source, saved, member, rank, fun x hx => oldBound x (bound x hx)⟩
    · exact ⟨i, Y, R, μ, K, η, C, L, V, q, cell, source, saved, member, rank, bound⟩
  · intro m s hm
    exact (entries m s).trans ⟨fun hs => hs.elim id (fun hs => (KP.mem_irrefl_d (ZF.modelsKP hZF) n (hs.1 ▸ hm)).elim), Or.inl⟩

/-- 树的两条后继边保留旧模型列，追加行因而仍指向它的实际产生结点。 -/
theorem Tg_past_d.links_push_l {ω n H n' H' N b' Q Q' i Y R μ K η C L V q c : M.Domain}
    (updated : Tg_past_d hZF ω n' H' N b') (succ : M.SuccessorOf n' n)
    (newest : Tg_past_at_d H' n i Y R μ K η C L V q)
    (entries : ∀ m r, M.mem m n → (Rd_entry_d m r H' ↔ Rd_entry_d m r H))
    (links : Tg_past_links_d I H Q) (keep : ∀ m d, Rd_entry_d m d Q → Rd_entry_d m d Q')
    (node : Rd_entry_d i c Q') (model : Smem_d I c Y R) : Tg_past_links_d I H' Q' := by
  intro m i₀ Y₀ R₀ μ₀ K₀ η₀ C₀ L₀ V₀ q₀ hm
  obtain ⟨r, hr, cell⟩ := hm
  have domain := (updated.sequence.2.2 m).mpr ⟨r, hr⟩
  rcases (succ m).mp domain with lt | eq
  · obtain ⟨d, hd, md⟩ := links m i₀ Y₀ R₀ μ₀ K₀ η₀ C₀ L₀ V₀ q₀ ⟨r, (entries m r lt).mp hr, cell⟩
    exact ⟨d, keep i₀ d hd, md⟩
  · have eq := hZF.1.eq_of_same_members m n eq
    subst m
    obtain ⟨s, hs, cell'⟩ := newest
    have eq := updated.sequence.2.1.2 n r s hr hs
    subst s
    have tuple := rt_tuple_inj_l cell cell'
    have ei : i₀ = i := congrFun tuple 0
    have eY : Y₀ = Y := congrFun tuple 1
    have eR : R₀ = R := congrFun tuple 2
    subst i₀ Y₀ R₀
    exact ⟨c, node, model⟩

/-- 按内部轮号选取旧源；其树结点、完整记录和当前共同层一次返回。 -/
theorem Tg_past_d.select_l {ω n H X b Q m : M.Domain} (h : Tg_past_d hZF ω n H X b)
    (links : Tg_past_links_d I H Q) (hm : M.mem m n) :
    ∃ i Y R μ K η C L V q c, Tg_past_at_d H m i Y R μ K η C L V q ∧ Rd_entry_d i c Q ∧ Smem_d I c Y R ∧
      Ic_model_d hZF ω μ K Y R ∧ Tg_saved_d I ω Y R η C L V q ∧ M.mem V X ∧ Vr_d X L V ∧ M.MemberSubset L b := by
  obtain ⟨r, hr⟩ := (h.sequence.2.2 m).mp hm
  obtain ⟨i, Y, R, μ, K, η, C, L, V, q, cell, source, saved, member, rank, bound⟩ := h.rows m r hr
  have ha : Tg_past_at_d H m i Y R μ K η C L V q := ⟨r, hr, cell⟩
  obtain ⟨c, node, model⟩ := links m i Y R μ K η C L V q ha
  exact ⟨i, Y, R, μ, K, η, C, L, V, q, c, ha, node, model, source, saved, member, rank, bound⟩

/-- 一个共同支撑层同时保存整段历史，无须逐轮重新构造旧回答。 -/
theorem Tg_past_d.transfer_l {ω n H X b N L W : M.Domain}
    (h : Tg_past_d hZF ω n H X b) (xt : M.TransitiveSet X) (nt : M.TransitiveSet N)
    (hW : M.mem W X) (rank : Vr_d X L W) (hW' : M.mem W N) (next : Vr_d N L W)
    (limit : M.IsLimitOrdinal L) (below : M.mem b L) :
    Tg_past_d hZF ω n H N b := by
  refine ⟨h.sequence, ?_⟩
  intro m r hr
  obtain ⟨i, Y, R, μ, K, η, C, ζ, V, q, cell, source, saved, hV, old, sub⟩ := h.rows m r hr
  have hζ := ordinal_down_l (ZF.modelsKP hZF) (old.ordinal_l hV) limit.1 sub below
  obtain ⟨hVW, inner⟩ := rank.rank_l hZF xt hW limit (rank.ordinal_subset_l hZF xt hW ζ hζ) hV old
  exact ⟨i, Y, R, μ, K, η, C, ζ, V, q, cell, source, saved, nt W hW' V hVW,
    next.of_rank_l nt hW' hVW inner, sub⟩

/-- 临界点高于历史界的偶数边逐点固定全部旧回答所在层。 -/
theorem Tg_past_d.fixed_l {ω n H X b κ W j : M.Domain}
    (h : Tg_past_d hZF ω n H X b) (xt : M.TransitiveSet X) (hW : M.mem W X) (rank : Vr_d X κ W)
    (below : M.MemberSubset b κ) (fixed : ∀ x, M.mem x W → Rd_entry_d x x j) : Tg_past_fixed_d H j := by
  intro m i Y R μ K η C L V q ha
  obtain ⟨_, _, hV, old, bound⟩ := h.read_l hZF ha
  have sub := (rank.compare_l hZF xt hW hV old (fun x hx => below x (bound x hx))).1
  exact fun x hx => fixed x (sub x hx)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一存档的树、长度及三张坐标图

奇数边必须连接原请求选中的历史行。树及三张坐标图都从同一完整记录
读取；恢复图的嵌入像添一个点，实数图和标签图保持原前缀。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_saved_branch_d (Y R ω V q S n s t g : M.Domain) : Prop :=
  ∃ v : Fin 54 → M.Domain, Tg_saved_code_d Y R ω V q v ∧ v 19 = S ∧ v 22 = n ∧ v 40 = s ∧ v 41 = t ∧ v 42 = g

def tg_saved_branch0_m : Formula 1 10 := rt_exists_m 54 (.conj
  (tg_saved_code_m (.bound 54) (.bound 55) (.bound 56) (.bound 57) (.bound 58)
    (fun i : Fin 54 => .bound (i.castAdd 10)))
  (set[64] ⟪⌜(.bound 19 : Term 64)⌝ₛ = ⌜(.bound 59 : Term 64)⌝ₛ ∧
    ⌜(.bound 22 : Term 64)⌝ₛ = ⌜(.bound 60 : Term 64)⌝ₛ ∧ ⌜(.bound 40 : Term 64)⌝ₛ = ⌜(.bound 61 : Term 64)⌝ₛ ∧
    ⌜(.bound 41 : Term 64)⌝ₛ = ⌜(.bound 62 : Term 64)⌝ₛ ∧ ⌜(.bound 42 : Term 64)⌝ₛ = ⌜(.bound 63 : Term 64)⌝ₛ⟫))

theorem tg_saved_branch0_closed_l : tg_saved_branch0_m.FreeClosed := by
  apply (rt_exists_closed_l _).mpr
  refine ⟨tg_saved_code_closed_l _ _ _ _ _ _ rfl rfl rfl rfl rfl (fun _ => rfl), ?_⟩
  simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]

theorem tg_saved_branch0_sat_l (hE : Extensional M) (ρ : Env M 10) :
    Formula.satisfies ρ tg_saved_branch0_m ↔ Tg_saved_branch_d (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) (ρ.bound 3) (ρ.bound 4) (ρ.bound 5) (ρ.bound 6) (ρ.bound 7) (ρ.bound 8) (ρ.bound 9) := by
  rw [tg_saved_branch0_m, rt_exists_sat_l]
  apply exists_congr
  intro v
  simp only [Formula.satisfies_conj_iff, tg_saved_code_sat_l, Formula.satisfies_extensionalEq_iff_eq hE, Term.eval_bound]
  have tuple : (fun i : Fin 54 => (rt_push_d ρ 54 v).bound (i.castAdd 10)) = v := funext (rt_push_new_l ρ v)
  rw [tuple]
  have o0 : (rt_push_d ρ 54 v).bound 54 = ρ.bound 0 := rt_push_old_l ρ v 0
  have o1 : (rt_push_d ρ 54 v).bound 55 = ρ.bound 1 := rt_push_old_l ρ v 1
  have o2 : (rt_push_d ρ 54 v).bound 56 = ρ.bound 2 := rt_push_old_l ρ v 2
  have o3 : (rt_push_d ρ 54 v).bound 57 = ρ.bound 3 := rt_push_old_l ρ v 3
  have o4 : (rt_push_d ρ 54 v).bound 58 = ρ.bound 4 := rt_push_old_l ρ v 4
  have o5 : (rt_push_d ρ 54 v).bound 59 = ρ.bound 5 := rt_push_old_l ρ v 5
  have o6 : (rt_push_d ρ 54 v).bound 60 = ρ.bound 6 := rt_push_old_l ρ v 6
  have o7 : (rt_push_d ρ 54 v).bound 61 = ρ.bound 7 := rt_push_old_l ρ v 7
  have o8 : (rt_push_d ρ 54 v).bound 62 = ρ.bound 8 := rt_push_old_l ρ v 8
  have o9 : (rt_push_d ρ 54 v).bound 63 = ρ.bound 9 := rt_push_old_l ρ v 9
  have n19 : (rt_push_d ρ 54 v).bound 19 = v 19 := rt_push_new_l ρ v 19
  have n22 : (rt_push_d ρ 54 v).bound 22 = v 22 := rt_push_new_l ρ v 22
  have n40 : (rt_push_d ρ 54 v).bound 40 = v 40 := rt_push_new_l ρ v 40
  have n41 : (rt_push_d ρ 54 v).bound 41 = v 41 := rt_push_new_l ρ v 41
  have n42 : (rt_push_d ρ 54 v).bound 42 = v 42 := rt_push_new_l ρ v 42
  simp only [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, n19, n22, n40, n41, n42]

def tg_saved_branch_m {d} (Y R ω V q S n s t g : Term d) : Formula 1 d :=
  tg_saved_branch0_m.bind (fun i => [Y,R,ω,V,q,S,n,s,t,g].get i)

@[simp] theorem tg_saved_branch_closed_l {d} (Y R ω V q S n s t g : Term d)
    (hY : Y.freeSupport = []) (hR : R.freeSupport = []) (hω : ω.freeSupport = []) (hV : V.freeSupport = []) (hq : q.freeSupport = []) (hS : S.freeSupport = []) (hn : n.freeSupport = []) (hs : s.freeSupport = []) (ht : t.freeSupport = []) (hg : g.freeSupport = []) : (tg_saved_branch_m Y R ω V q S n s t g).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _ (Fin.cases hY (Fin.cases hR (Fin.cases hω (Fin.cases hV (Fin.cases hq (Fin.cases hS (Fin.cases hn (Fin.cases hs (Fin.cases ht (Fin.cases hg (fun i => Fin.elim0 i))))))))))) _).mpr tg_saved_branch0_closed_l

theorem tg_saved_branch_sat_l (hE : Extensional M) {d} (ρ : Env M d) (Y R ω V q S n s t g : Term d) :
    Formula.satisfies ρ (tg_saved_branch_m Y R ω V q S n s t g) ↔ Tg_saved_branch_d (Y.eval ρ) (R.eval ρ) (ω.eval ρ) (V.eval ρ) (q.eval ρ) (S.eval ρ) (n.eval ρ) (s.eval ρ) (t.eval ρ) (g.eval ρ) := by
  rw [tg_saved_branch_m, Formula.satisfies_bind, tg_saved_branch0_sat_l hE]
  rfl

def Tg_odd_d (ω H ξ α k G e t ℓ Sₑ S n s g : M.Domain) : Prop :=
  (t = e ∧ k = ξ ∧ g = e ∧ ∃ j, It_map_d G ξ α j ∧ Rd_entry_d Sₑ S j) ∨
  (t ≠ e ∧ ∃ Y R μ K η C L V q S₀ n₀ s₀ t₀ g₀ j a b z,
    Tg_past_at_d H ℓ k Y R μ K η C L V q ∧ Tg_saved_branch_d Y R ω V q S₀ n₀ s₀ t₀ g₀ ∧
    It_map_d G k α j ∧ Rd_entry_d S₀ S j ∧ Rd_entry_d n₀ b j ∧ Rd_entry_d g₀ a j ∧
    M.SuccessorOf n b ∧ Rd_entry_d b z g ∧ (∀ p, M.mem p g ↔ M.mem p a ∨ KPair_d M p b z) ∧
    Rd_entry_d s₀ s₀ j ∧ M.MemberSubset s₀ s ∧ Rd_entry_d t₀ t₀ j ∧ M.MemberSubset t₀ t)

def tg_odd_m {d} (ω H ξ α k G e t ℓ Sₑ S n s g : Term d) : Formula 1 d := set[d] ⟪
  (⌜t⌝ₛ = ⌜e⌝ₛ ∧ ⌜k⌝ₛ = ⌜ξ⌝ₛ ∧ ⌜g⌝ₛ = ⌜e⌝ₛ ∧
    (∃ j, ⌜it_map_m⌝ₚ(⌜G⌝ₛ, ⌜ξ⌝ₛ, ⌜α⌝ₛ, j) ∧ ⌜rd_entry0_m⌝ₚ(⌜Sₑ⌝ₛ, ⌜S⌝ₛ, j))) ∨
  (¬ (⌜t⌝ₛ = ⌜e⌝ₛ) ∧ (∃ Y R μ K η C L V q S₀ n₀ s₀ t₀ g₀ j a b z,
    ⌜tg_past_at_m⌝ₚ(⌜H⌝ₛ, ⌜ℓ⌝ₛ, ⌜k⌝ₛ, Y, R, μ, K, η, C, L, V, q) ∧
    ⌜tg_saved_branch_m⌝ₚ(Y, R, ⌜ω⌝ₛ, V, q, S₀, n₀, s₀, t₀, g₀) ∧ ⌜it_map_m⌝ₚ(⌜G⌝ₛ, ⌜k⌝ₛ, ⌜α⌝ₛ, j) ∧
    ⌜rd_entry0_m⌝ₚ(S₀, ⌜S⌝ₛ, j) ∧ ⌜rd_entry0_m⌝ₚ(n₀, b, j) ∧ ⌜rd_entry0_m⌝ₚ(g₀, a, j) ∧
    ⌜KP.succ0_m⌝ₚ(⌜n⌝ₛ, b) ∧ ⌜rd_entry0_m⌝ₚ(b, z, ⌜g⌝ₛ) ∧
    (∀ p, p ∈ ⌜g⌝ₛ ↔ p ∈ a ∨ ⌜kpair0_m⌝ₚ(p, b, z)) ∧
    ⌜rd_entry0_m⌝ₚ(s₀,s₀,j) ∧ s₀ ⊆ ⌜s⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(t₀,t₀,j) ∧ t₀ ⊆ ⌜t⌝ₛ))⟫
derive_free_closed tg_odd_m

theorem tg_odd_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω H ξ α k G e t ℓ Sₑ S n s g : Term d) :
    Formula.satisfies ρ (tg_odd_m ω H ξ α k G e t ℓ Sₑ S n s g) ↔
      Tg_odd_d (ω.eval ρ) (H.eval ρ) (ξ.eval ρ) (α.eval ρ) (k.eval ρ) (G.eval ρ)
        (e.eval ρ) (t.eval ρ) (ℓ.eval ρ) (Sₑ.eval ρ) (S.eval ρ) (n.eval ρ) (s.eval ρ) (g.eval ρ) := by
  simp only [tg_odd_m, Tg_odd_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_exists_iff,
    tg_past_at_sat_l hE, tg_saved_branch_sat_l hE, it_map_sat_l hE, rd_entry0_sat_l hE,
    KP.succ0_sat_l hE, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_subset_iff, kpair0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原超幂更新同时推进整列回答历史

共同支撑层保存此前全部行；本轮完整回答在产生它的奇数模型中打包，
再追加到内部历史。旧记录对应的四个低坐标和回答有序对沿偶数边固定。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 同一次真实树更新延伸任意已有有限历史，保留旧行、低坐标和树结点对应。 -/
def Tg_past_update_d (ω X κ i Y R μ K η C L V N κ' j Q Q' : M.Domain) (v : Fin 54 → M.Domain) : Prop :=
  ∀ n H b, M.mem n ω → Tg_past_d hZF ω n H X b → M.mem b κ → Tg_past_links_d I H Q →
    ∃ n' H' q, M.mem n' ω ∧ M.SuccessorOf n' n ∧ Tg_past_d hZF ω n' H' N κ' ∧
      Tg_saved_d I ω Y R η C L V q ∧ Tg_saved_code_d Y R ω V q v ∧ Tg_past_at_d H' n i Y R μ K η C L V q ∧
      (∀ m r, M.mem m n → (Rd_entry_d m r H' ↔ Rd_entry_d m r H)) ∧
      Tg_past_fixed_d H j ∧ Tg_past_links_d I H' Q'

/-- 任意内部有限历史都能加入本次实际回答，而不改变旧行。 -/
theorem Tg_past_d.answer_l {ω n H Y b R μ K η C L V N κ i : M.Domain}
    (past : Tg_past_d hZF ω n H Y b) (hn : M.mem n ω)
    (context : Tg_context_d I ω Y R η C) (source : Ic_model_d hZF ω μ K Y R)
    (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 54)
    (valid : Formula.satisfies ρ tg_round0_m) (hw : (ρ.bound 16).val = ω)
    (limit : M.IsLimitOrdinal L) (member : M.mem V C) (rank : Vr_d Y L V)
    (below : M.mem (ρ.bound 15).val L) (answer : M.mem (ρ.bound 11).val V)
    (nt : M.TransitiveSet N) (hVN : M.mem V N) (next : Vr_d N L V)
    (oldBound : M.mem b L) (bound : M.MemberSubset L κ) :
    ∃ n' H' q, M.mem n' ω ∧ M.SuccessorOf n' n ∧ Tg_past_d hZF ω n' H' N κ ∧
      Tg_saved_d I ω Y R η C L V q ∧ Tg_saved_code_d Y R ω V q (fun i => (ρ.bound i).val) ∧
      Tg_past_at_d H' n i Y R μ K η C L V q ∧
      ∀ m r, M.mem m n → (Rd_entry_d m r H' ↔ Rd_entry_d m r H) := by
  obtain ⟨q, saved, code⟩ := context.save_round_l hZF source.source nc ρ valid hw limit member rank below answer
  obtain ⟨n', succ, finite⟩ := source.source.omega.1.2 n hn
  have carried := past.transfer_l hZF source.source.transitive nt
    (source.source.transitive C context.member V member) rank hVN next limit oldBound
  obtain ⟨H', updated, newest, entries⟩ := carried.push_l hZF succ source saved hVN next
    (fun x hx => bound x (limit.1.transitive b oldBound x hx)) bound (i := i)
  exact ⟨n', H', q, finite, succ, updated, saved, code, newest, entries⟩

/-- 先到本轮奇数源，再到新偶数源；两次共同秩段比较覆盖全部旧行。 -/
theorem Tg_context_d.past_update_l {ω X κ i Y R μ K η C θ U L V N κ' j W Q Q' c : M.Domain}
    (context : Tg_context_d I ω Y R η C) (source : Ic_model_d hZF ω μ K Y R)
    (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 54)
    (valid : Formula.satisfies ρ tg_round0_m) (hw : (ρ.bound 16).val = ω)
    (xt : M.TransitiveSet X) (hUX : M.mem U X) (left : Vr_d X θ U)
    (hUY : M.mem U Y) (right : Vr_d Y θ U) (hθ : M.IsLimitOrdinal θ) (hκθ : M.MemberSubset κ θ)
    (limit : M.IsLimitOrdinal L) (member : M.mem V C) (rank : Vr_d Y L V)
    (below : M.mem (ρ.bound 15).val L) (answer : M.mem (ρ.bound 11).val V) (hκL : M.MemberSubset κ L)
    (nt : M.TransitiveSet N) (hVN : M.mem V N) (next : Vr_d N L V) (bound : M.MemberSubset L κ')
    (hW : M.mem W X) (fixedRank : Vr_d X κ W) (fixed : ∀ x, M.mem x W → Rd_entry_d x x j)
    (keep : ∀ m d, Rd_entry_d m d Q → Rd_entry_d m d Q') (node : Rd_entry_d i c Q') (model : Smem_d I c Y R) :
    Tg_past_update_d hZF ω X κ i Y R μ K η C L V N κ' j Q Q' (fun i => (ρ.bound i).val) := by
  intro n H b hn past hb links
  have odd := past.transfer_l hZF xt source.source.transitive hUX left hUY right hθ (hκθ b hb)
  obtain ⟨n', H', q, finite, succ, updated, saved, code, newest, entries⟩ := odd.answer_l hZF hn context source nc ρ
    valid hw limit member rank below answer nt hVN next (hκL b hb) bound (i := i)
  have critical := fixedRank.ordinal_l hW
  exact ⟨n', H', q, finite, succ, updated, saved, code, newest, entries,
    past.fixed_l hZF xt hW fixedRank (critical.transitive b hb) fixed,
    updated.links_push_l hZF succ newest entries links keep node model⟩

/-- 由层的逐点固定性得到原回答的固定性；配对见证来自原反射层。 -/
theorem Tg_saved_d.answer_fixed_l {ω Y R η C L V q j c : M.Domain}
    (saved : Tg_saved_d I ω Y R η C L V q) (model : Smem_d I c Y R) (trans : M.TransitiveSet Y)
    (fixed : ∀ x, M.mem x V → Rd_entry_d x x j) (nc : Nonempty {x // M.mem x C}) :
    ∃ ρ : Env (rt_model_l C nc) 54, Tg_saved_code_d Y R ω V q (fun i => (ρ.bound i).val) ∧
      Formula.satisfies ρ tg_round0_m ∧ (ρ.bound 16).val = ω ∧
      Rd_entry_d (ρ.bound 15).val (ρ.bound 15).val j ∧ Rd_entry_d (ρ.bound 13).val (ρ.bound 13).val j ∧
      Rd_entry_d (ρ.bound 12).val (ρ.bound 12).val j ∧ Rd_entry_d (ρ.bound 11).val (ρ.bound 11).val j ∧
      ∀ a, KPair_d M a (ρ.bound 15).val (ρ.bound 11).val → Rd_entry_d a a j := by
  obtain ⟨ρ, code, valid, hw, hτ, hU, hD, hw'⟩ :=
    saved.membership_l I hZF.1 model (trans C saved.context.member) nc
  have hV := ((model.2 V C).mp saved.member).1
  refine ⟨ρ, code, valid, hw, fixed _ hτ, fixed _ hU, fixed _ hD, fixed _ hw', ?_⟩
  intro a pair
  let nx := model.1.2.1
  let N₀ := smdl_structure_l I (R := R) nx
  let V₀ : N₀.Domain := ⟨V, hV⟩
  let t : N₀.Domain := ⟨(ρ.bound 15).val, trans V hV _ hτ⟩
  let w : N₀.Domain := ⟨(ρ.bound 11).val, trans V hV _ hw'⟩
  have en := saved.ext.native_l I nx
  have fs := saved.context.finite_l nx en
  have tv : N₀.mem t V₀ := (model.2 _ V).mpr ⟨t.property, hV, hτ⟩
  have wv : N₀.mem w V₀ := (model.2 _ V).mpr ⟨w.property, hV, hw'⟩
  obtain ⟨p, _, pk⟩ := fs.kpair_l (fs.transitive V₀ saved.member t tv) (fs.transitive V₀ saved.member w wv)
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨ω, saved.context.omega_mem⟩⟩
  let ε : Env (rt_model_l Y ny) 3 := ⟨Fin.cases p (Fin.cases t (fun _ => w)), fun _ => p⟩
  have pk : KPair_d M p.val t.val w.val := (kpair0_sat_l hZF.1 ..).mp
    ((rt_model_delta_l trans ny (kpair0_delta_l .newest (.bound 1) (.bound 2)) ε).mp
      ((smem_formula_l I model ny _ ε).mpr ((kpair0_sat_l en ..).mpr pk)))
  have ha : M.mem a Y := kpair_unique_l M hZF.1 pk pair ▸ p.property
  exact fixed a ((saved.rank_l I (ZF.modelsKP hZF) trans model).kpair_mem_l hZF trans hV
    (saved.limit_l I (ZF.modelsKP hZF) trans model) hτ hw' ha pair)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 各存档中的树都是同一原树的根嵌入像

树名沿真实根图保存。重置使用恒等边上的实际条目，继续使用被选旧行的
原树像；两种情形都由图表复合律给出新行的树名。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_root_tree_d (ω H G o S₀ : M.Domain) : Prop := ∀ m i Y R μ K η C L V q S n s t g,
  Tg_past_at_d H m i Y R μ K η C L V q → Tg_saved_branch_d Y R ω V q S n s t g →
    ∃ j, It_map_d G o i j ∧ Rd_entry_d S₀ S j

def tg_root_tree_m {d} (ω H G o S₀ : Term d) : Formula 1 d := set[d] ⟪∀ m i Y R μ K η C L V q S n s t g,
  ⌜tg_past_at_m⌝ₚ(⌜H⌝ₛ, m, i, Y, R, μ, K, η, C, L, V, q) →
  ⌜tg_saved_branch_m⌝ₚ(Y, R, ⌜ω⌝ₛ, V, q, S, n, s, t, g) →
  (∃ j, ⌜it_map_m⌝ₚ(⌜G⌝ₛ, ⌜o⌝ₛ, i, j) ∧ ⌜rd_entry0_m⌝ₚ(⌜S₀⌝ₛ, S, j))⟫
derive_free_closed tg_root_tree_m

theorem tg_root_tree_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω H G o S₀ : Term d) :
    Formula.satisfies ρ (tg_root_tree_m ω H G o S₀) ↔
      Tg_root_tree_d (ω.eval ρ) (H.eval ρ) (G.eval ρ) (o.eval ρ) (S₀.eval ρ) := by
  simp only [tg_root_tree_m, Tg_root_tree_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, tg_past_at_sat_l hE,
    tg_saved_branch_sat_l hE, it_map_sat_l hE, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]; rfl

def Tg_common_tree_d (ω H G o π S : M.Domain) : Prop :=
  ∃ S₀, Rd_entry_d S₀ S π ∧ Tg_root_tree_d ω H G o S₀

def tg_common_tree_m {d} (ω H G o π S : Term d) : Formula 1 d := set[d] ⟪∃ S₀,
  ⌜rd_entry0_m⌝ₚ(S₀, ⌜S⌝ₛ, ⌜π⌝ₛ) ∧ ⌜tg_root_tree_m⌝ₚ(⌜ω⌝ₛ, ⌜H⌝ₛ, ⌜G⌝ₛ, ⌜o⌝ₛ, S₀)⟫
derive_free_closed tg_common_tree_m

theorem tg_common_tree_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω H G o π S : Term d) :
    Formula.satisfies ρ (tg_common_tree_m ω H G o π S) ↔
      Tg_common_tree_d (ω.eval ρ) (H.eval ρ) (G.eval ρ) (o.eval ρ) (π.eval ρ) (S.eval ρ) := by
  simp only [tg_common_tree_m, Tg_common_tree_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE, tg_root_tree_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem Tg_saved_branch_d.tree_unique_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {Y R ω V q S n s t g S' n' s' t' g' : M.Domain}
    (h : Tg_saved_branch_d Y R ω V q S n s t g) (h' : Tg_saved_branch_d Y R ω V q S' n' s' t' g') : S = S' := by
  obtain ⟨v, code, hs, _⟩ := h
  obtain ⟨w, pack, hs', _⟩ := h'
  exact hs.symm.trans ((congrFun (code.inj_l I hE pack) 21).trans hs')

theorem tg_root_tree_empty_l {ω H G o S : M.Domain} (empty : ∀ x, ¬ M.mem x H) : Tg_root_tree_d ω H G o S :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨_, ⟨p, _, hp⟩, _⟩ _ => (empty p hp).elim

theorem Tg_root_tree_d.extend_l {ω H G G' o S : M.Domain} (h : Tg_root_tree_d ω H G o S)
    (keep : ∀ i j, It_map_d G o i j → It_map_d G' o i j) : Tg_root_tree_d ω H G' o S := by
  intro m i Y R μ K η C L V q S' n a b g row br
  obtain ⟨j, hj, image⟩ := h m i Y R μ K η C L V q S' n a b g row br
  exact ⟨j, keep i j hj, image⟩

variable (hZF : M.Models ZF)

theorem Tg_root_tree_d.push_l {ω n H n' H' X b G o S₀ i Y R μ K η C L V q S k s t g j : M.Domain}
    (past : Tg_past_d hZF ω n' H' X b) (succ : M.SuccessorOf n' n)
    (newest : Tg_past_at_d H' n i Y R μ K η C L V q)
    (entries : ∀ m r, M.mem m n → (Rd_entry_d m r H' ↔ Rd_entry_d m r H))
    (old : Tg_root_tree_d ω H G o S₀) (br : Tg_saved_branch_d Y R ω V q S k s t g)
    (root : It_map_d G o i j) (image : Rd_entry_d S₀ S j) : Tg_root_tree_d ω H' G o S₀ := by
  intro m i' Y' R' μ' K' η' C' L' V' q' S' k' a' b' g' row branch
  obtain ⟨r, hr, cell⟩ := row
  rcases (succ m).mp ((past.sequence.2.2 m).mpr ⟨r, hr⟩) with lt | eq
  · exact old m i' Y' R' μ' K' η' C' L' V' q' S' k' a' b' g' ⟨r, (entries m r lt).mp hr, cell⟩ branch
  · have eq := hZF.1.eq_of_same_members m n eq
    subst m
    obtain ⟨s, hs, pack⟩ := newest
    have eq := past.sequence.2.1.2 n s r hs hr
    subst s
    have eq := rt_tuple_inj_l cell pack
    have ei : i' = i := congrFun eq 0
    have eY : Y' = Y := congrFun eq 1
    have eR : R' = R := congrFun eq 2
    have eV : V' = V := congrFun eq 8
    have eq : q' = q := congrFun eq 9
    subst i' Y' R' V' q'
    exact ⟨j, root, (branch.tree_unique_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1 br).symm ▸ image⟩

theorem Tg_root_tree_d.odd_l {ω H G G' o S₀ Sₑ S n s g ξ α k e t ℓ π π' β T Q : M.Domain}
    (h : Tg_root_tree_d ω H G o S₀) (keep : ∀ i j, It_map_d G o i j → It_map_d G' o i j)
    (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω β T Q G') (old : It_map_d G' o ξ π) (image : Rd_entry_d S₀ Sₑ π)
    (root : It_map_d G' o α π') (odd : Tg_odd_d ω H ξ α k G' e t ℓ Sₑ S n s g) : Rd_entry_d S₀ S π' := by
  rcases odd with ⟨_, _, _, j, edge, value⟩ | ⟨_, Y, R, μ, K, η, C, L, V, q, S', n', s', t', g', j, _, _, _, row, br, edge, value, _⟩
  · exact diagram.comp o ξ α π j π' old edge root S₀ Sₑ S image value
  · obtain ⟨r, hr, hs⟩ := h ℓ k Y R μ K η C L V q S' n' s' t' g' row br
    exact diagram.comp o k α r j π' (keep k r hr) edge root S₀ S' S hs value

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 完整回答的有限图与回答基底

在原反射层一次读取固定54项坐标。图、后继和标签随后沿层的传递性读到所属结构，
避免各个复制消费者在多重原模型子类型中重复展开同一大公式。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Tg_round_parts_d (I : kpair_convention_l.Interpretation M)
    {C : M.Domain} (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 54) : Prop where
  language : Formula.satisfies (Definitional.Env.substitute ρ
    (fun j : Fin 10 => [.bound 16,.bound 15,.bound 24,.bound 14,.bound 13,
      .bound 12,.bound 6,.bound 5,.bound 4,.bound 3].get j)) ee_language0_m
  elastic : (M.mem (ρ.bound 6).val (ρ.bound 11).val ∧ M.mem (ρ.bound 5).val (ρ.bound 11).val) ∧
    M.mem (ρ.bound 4).val (ρ.bound 11).val ∧ M.mem (ρ.bound 3).val (ρ.bound 11).val
  height : M.mem (ρ.bound 0).val (ρ.bound 11).val
  empty : ∀ x, ¬ M.mem x (ρ.bound 17).val
  empty_omega : M.mem (ρ.bound 17).val (ρ.bound 16).val
  first : M.SuccessorOf (ρ.bound 23).val (ρ.bound 22).val
  last : M.SuccessorOf (ρ.bound 24).val (ρ.bound 23).val
  finite : M.mem (ρ.bound 24).val (ρ.bound 16).val
  graph : Tg_graph_d I (ρ.bound 22).val (ρ.bound 40).val
  labels : Fn0_d (ρ.bound 22).val (ρ.bound 16).val (ρ.bound 41).val
  reply : Formula.satisfies (ρ.reindex (fun j => [16,17,23,24,2,1,0].get j)) tg_reply_base0_m

theorem tg_round_parts_l (hKP : M.Models KP) {ω C : M.Domain}
    (fs : Fs_read_d ω C) (nc : Nonempty {x // M.mem x C})
    (ρ : Env (rt_model_l C nc) 54) (round : Formula.satisfies ρ tg_round0_m) :
    Tg_round_parts_d (kp_pair_l hKP) nc ρ := by
  have data := ((Formula.satisfies_conj_iff ..).mp round).2
  simp only [tg_witness0_m,tg_round_m,Formula.satisfies_conj_iff] at data
  obtain ⟨_,_,_,_,_,_,language,_,elastic,replyLanguage,_,_,heightMember,_⟩ := data
  let f : Fin 10 → Term 54 := fun j => [.bound 16,.bound 15,.bound 24,.bound 14,.bound 13,
    .bound 12,.bound 6,.bound 5,.bound 4,.bound 3].get j
  have language : Formula.satisfies (Definitional.Env.substitute ρ f) ee_language0_m :=
    (Formula.satisfies_bind ρ f ee_language0_m).mp language
  simp only [ee_elastic_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at elastic
  have seed := ((Formula.satisfies_conj_iff ..).mp round).1
  simp only [tg_seed0_m,Formula.satisfies_rename,tg_seed_m,Formula.satisfies_conj_iff] at seed
  obtain ⟨_,empty,emptyω,_,_,_,_,first,last,_,_,_,real,_,_,_,_,_,_,node,_,_,_,labels⟩ := seed
  have graph : Tg_graph_d (kp_pair_l hKP) (ρ.bound 22).val (ρ.bound 40).val :=
    (tg_graph_source_l fs.transitive nc hKP.1 (KP.exists_pair hKP) _ _ _).mp
      ((Formula.satisfies_conj_iff ..).mp node).1
  have first := (rt_successor_l fs.transitive nc hKP.1 (ρ.bound 23) (ρ.bound 22)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp first)
  have last := (rt_successor_l fs.transitive nc hKP.1 (ρ.bound 24) (ρ.bound 23)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp last)
  simp only [tt_realized_m,Formula.satisfies_bind,tt_realized0_m,Formula.satisfies_conj_iff] at real
  have labels_ref : Formula.satisfies ρ (fn0_m (.bound 22) (.bound 16) (.bound 41)) :=
    (fn0_sat_l (rt_model_ext_l hKP.1 fs.transitive nc) ρ (.bound 22) (.bound 16) (.bound 41)).mpr
      ((fn0_sat_l (rt_model_ext_l hKP.1 fs.transitive nc) _ (.bound 6) (.bound 0) (.bound 25)).mp labels)
  have labels : Fn0_d (ρ.bound 22).val (ρ.bound 16).val (ρ.bound 41).val :=
    (fn0_sat_l hKP.1 _ (.bound 22) (.bound 16) (.bound 41)).mp
      ((rt_model_delta_l fs.transitive nc (fn0_delta_l (.bound 22) (.bound 16) (.bound 41)) ρ).mp labels_ref)
  simp only [tg_reply_language_m,Formula.satisfies_bind,tg_reply_language0_m,
    Formula.satisfies_conj_iff] at replyLanguage
  obtain ⟨_,_,_,_,_,_,_,_,_,_,base⟩ := replyLanguage
  have reply : Formula.satisfies (ρ.reindex (fun j => [16,17,23,24,2,1,0].get j)) tg_reply_base0_m := by
    simp only [tg_reply_base_m,Formula.satisfies_bind] at base
    apply (Formula.closed_env_l tg_reply_base0_m tg_reply_base0_closed_l ?_).mp base
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))) j
  exact ⟨language,elastic,heightMember,fun x hx => (Formula.satisfies_isEmpty_iff ..).mp empty
    ⟨x,fs.transitive (ρ.bound 17).val (ρ.bound 17).property x hx⟩ hx,
    emptyω,first,last,real.2.1,graph,labels,reply⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 完整原存档在实际传递目标中的节点

原节点无需传递。完整56项记录沿同一初等图进入目标反射层，再从同一回答读取长度及三张图。
有限节点的绝对读取只需该反射层传递，不对整个目标增加ZF或外部闭性要求。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem tg_round_node_l (hKP : M.Models KP) {ω C : M.Domain} (hw : M.IsOmega ω)
    (ct : M.TransitiveSet C) (nc : Nonempty {x // M.mem x C})
    (ρ : Env (rt_model_l C nc) 54) (round : Formula.satisfies ρ tg_round0_m)
    (natural : (ρ.bound 16).val = ω) : M.mem (ρ.bound 22).val ω ∧
      Tg_node_d (kp_pair_l hKP) (ρ.bound 22).val (ρ.bound 19).val
        (ρ.bound 40).val (ρ.bound 41).val (ρ.bound 42).val := by
  have seed := ((Formula.satisfies_conj_iff ..).mp round).1
  simp only [tg_seed0_m,Formula.satisfies_rename,tg_seed_m,Formula.satisfies_conj_iff] at seed
  obtain ⟨_,_,_,_,_,_,_,first,last,_,_,_,realized,_,_,_,_,_,_,node,_⟩ := seed
  simp only [tt_realized_m,Formula.satisfies_bind,tt_realized0_m,Formula.satisfies_conj_iff] at realized
  have finite : M.mem (ρ.bound 24).val ω := natural ▸ realized.2.1
  have first := (rt_successor_l ct nc hKP.1 (ρ.bound 23) (ρ.bound 22)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp first)
  have last := (rt_successor_l ct nc hKP.1 (ρ.bound 24) (ρ.bound 23)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp last)
  have finite := hw.transitive hKP _ (hw.transitive hKP _ finite _ last.predecessor_mem) _ first.predecessor_mem
  let ε := ρ.reindex (fun i : Fin 38 => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
  have node : Tg_node_d (kp_pair_l hKP) (ρ.bound 22).val (ρ.bound 19).val
      (ρ.bound 40).val (ρ.bound 41).val (ρ.bound 42).val :=
    (tg_node_source_l ct nc hKP.1 (KP.exists_pair hKP) ε
      (.bound 6) (.bound 3) (.bound 24) (.bound 25) (.bound 26)).mp node
  exact ⟨finite,node⟩

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 同一完整原存档沿真实图产生全部坐标像及目标中的实际有限节点。 -/
theorem Tg_saved_d.image_node_l {Ω w c X R η C L V q z d Y S j : M.Domain} {v : Fin 54 → M.Domain}
    (saved : Tg_saved_d I w X R η C L V q) (hw : M.IsOmega Ω)
    (model : Smdl_d I c X R) (numbers : Rr_layer_d I Ω X R w z)
    (target : Smem_d I d Y S) (yt : M.TransitiveSet Y) (map : Smap_d I Ω c d X Y j)
    (code : Tg_saved_code_d X R w V q v) : ∃ u : Fin 54 → M.Domain,
      (∀ i, Rd_entry_d (v i) (u i) j) ∧ M.mem (u 22) Ω ∧ Tg_node_d I (u 22) (u 19) (u 40) (u 41) (u 42) := by
  have number := numbers.omega_image_mem_l I hZF hw saved.ext model target yt map
  obtain ⟨η',C',_,imageC,context⟩ := saved.context.map_l hZF hw model target.1 map number.1
  have ct := (context.rank_l (ZF.modelsKP hZF) yt ⟨d,target⟩).transitive_l yt context.member
  let nc : Nonempty {x // M.mem x C'} := ⟨⟨Ω,context.omega_l ⟨d,target⟩⟩⟩
  let N := smdl_structure_l I (R := S) target.1.2.1
  let Cn : N.Domain := ⟨C',context.member⟩
  let nd : Nonempty {x : N.Domain // N.mem x Cn} :=
    ⟨⟨⟨Ω,context.omega_mem⟩,(target.2 Ω C').mpr ⟨context.omega_mem,context.member,context.omega_l ⟨d,target⟩⟩⟩⟩
  obtain ⟨_,σ,_,images,_,_,valid⟩ := map.record_image_l I hZF hw model target.1
    (smem_ext_l I target.1 target.2 yt hZF.1) Cn imageC (target.slice_transitive_l I Cn ct)
      nd tg_saved_record0_m tg_saved_record0_closed_l saved.record ((tg_saved_code_read_l I hZF.1).mp code).2
  let θ := target.slice_env_d I Cn nd nc σ
  have valid : Formula.satisfies θ tg_saved_record0_m :=
    (target.slice_formula_l I Cn (yt C' context.member) nd nc tg_saved_record0_m σ).mp valid
  obtain ⟨round,links⟩ := (Formula.satisfies_conj_iff ..).mp valid
  let ρ : Env (rt_model_l C' nc) 54 := ⟨fun i => θ.bound i.succ.succ,fun _ => θ.bound 0⟩
  have round : Formula.satisfies ρ tg_round0_m :=
    (Formula.closed_env_l tg_round0_m tg_round0_closed_l
      (ρ := θ.reindex (fun i : Fin 54 => i.succ.succ)) (η := ρ) rfl).mp
      ((Formula.satisfies_rename ..).mp round)
  have natural : (ρ.bound 16).val = Ω := by
    simp only [Formula.satisfies_conj_iff,Formula.satisfies_extensionalEq_iff_eq (rt_model_ext_l hZF.1 ct nc)] at links
    have eq : (θ.bound 18).val = (θ.bound 0).val := congrArg Subtype.val links.1
    exact eq.trans (map.1.1.1.2 w _ Ω (images 0) number.1)
  obtain ⟨finite,node⟩ := tg_round_node_l (ZF.modelsKP hZF) hw ct nc ρ round natural
  exact ⟨(fun i => (ρ.bound i).val),fun i => images i.succ.succ,finite,node⟩

end YesMetaZFC.SetTheory.LargeCardinal
