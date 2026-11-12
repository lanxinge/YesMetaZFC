import YesMetaZFC.SetTheory.LargeCardinal.Game.RigidAssemble
import YesMetaZFC.SetTheory.LargeCardinal.Game.RecoverySyntax
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativePlay
import YesMetaZFC.SetTheory.LargeCardinal.Game.Basis
import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNode
import YesMetaZFC.SetTheory.LargeCardinal.Game.Round
import YesMetaZFC.SetTheory.LargeCardinal.Game.Rank
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CriticalBound
import YesMetaZFC.SetTheory.CumulativeRelativeRestriction
import YesMetaZFC.SetTheory.LargeCardinal.Game.Recovery
import YesMetaZFC.SetTheory.LargeCardinal.Game.Restart
import YesMetaZFC.SetTheory.LargeCardinal.Game.QueryTransfer
import YesMetaZFC.SetTheory.LargeCardinal.Types.ContinueAbsolute
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.WorkingApply
import YesMetaZFC.Model.SetTheory.Types.SubtypeReflect
import YesMetaZFC.Model.SetTheory.Embedding.Relative
import YesMetaZFC.Model.SetTheory.Types.SubtypeUp

/-! # 从当前继续输入读取唯一高度

旧回答基底已沿实际根图搬运。这里只识别同一候选的常量域，并把原
超过关系与 dcp 定义域送入高度刚性句子，得到字面的最大序数查询成员。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω X C η : M.Domain} (nc : Nonempty {x // M.mem x C})
  (ρ : Env (rt_model_l C nc) 29) (χ ψ : Env (rt_model_l C nc) 12) (ε : Env (rt_model_l C nc) 7)
local notation "N" => rt_model_l C nc
local notation "p" => (fun i => Subtype.val (Env.bound ρ i))

theorem Tg_context_d.rigid_l {κ K R γ Z : M.Domain}
    (context : Tg_context_d I ω X R η C) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (hZ : M.mem Z X) (rankZ : Vr_d X γ Z) (lower : M.MemberSubset γ (p 1))
    (low : M.mem (ψ.bound 4).val Z ∧ M.mem (ψ.bound 5).val Z ∧ M.mem (ψ.bound 6).val Z)
    (hw : p 0 = ω) (ωχ : (χ.bound 2).val = ω) (τχ : (χ.bound 3).val = p 8)
    (uχ : (χ.bound 0).val = p 13) (mχ : (χ.bound 1).val = p 9)
    (ωψ : (ψ.bound 0).val = ω) (lψ : (ψ.bound 2).val = (χ.bound 4).val)
    (nψ : (ψ.bound 3).val = p 9) (eψ : (ψ.bound 1).val = (ε.bound 1).val)
    (ωε : (ε.bound 0).val = ω) (nε : (ε.bound 3).val = p 3)
    (hi : M.mem (ε.bound 2).val (p 3)) (hh : M.mem (ε.bound 6).val (p 7))
    (seed : Formula.satisfies ρ tc_seed0_m) (candidate : Formula.satisfies χ tg_candidate0_m)
    (queries : Formula.satisfies ψ tg_query_row0_m) (reply : Formula.satisfies ε tg_reply_base0_m) :
    (χ.bound 6).val = p 11 ∧
      (M.mem (ψ.bound 4).val (χ.bound 6).val ∧ M.mem (ψ.bound 5).val (χ.bound 6).val ∧
        M.mem (ψ.bound 6).val (χ.bound 6).val) ∧ M.mem (ψ.bound 8).val (p 13) := by
  have fs := (context.read_l hZF source).1
  have data := seed
  simp only [tc_seed0_m, Formula.satisfies_conj_iff] at data
  obtain ⟨_, _, _, _, _, oldRank, oldConstants, _, exceeds, _⟩ := data
  have language := ((Formula.satisfies_conj_iff ..).mp candidate).1
  simp only [Formula.satisfies_rename, ee_language0_m, Formula.satisfies_conj_iff] at language
  obtain ⟨_, limit, newRank, constants, _⟩ := language
  have rank₀ := (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc ρ (.bound 8) (.bound 10)).mp oldRank
  have rank₁ := (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc χ (.bound 3) (.bound 5)).mp newRank
  have eqB := rank₀.unique_l hZF fs.transitive (ρ.bound 10).property (χ.bound 5).property
    (Eq.mp (congrArg (fun a => Vr_d C a (χ.bound 5).val) τχ) rank₁)
  have cons₀ := (rt_model_delta_l fs.transitive nc (tt_constants0_delta_l ..) ρ).mp oldConstants
  have cons₁ := (rt_model_delta_l fs.transitive nc (tt_constants0_delta_l (.bound 1) (.bound 3) (.bound 4))
    (χ.reindex (fun i : Fin 10 => i.succ.succ))).mp constants
  simp only [tt_constants0_sat_l hZF.1, @eval_image_env_l N M Subtype.val] at cons₀ cons₁
  have eqV : (χ.bound 6).val = p 11 := hZF.1.eq_of_same_members _ _ (fun a =>
    (cons₁ a).trans ((or_congr (Iff.of_eq (congrArg (fun B => M.mem a B) eqB.symm))
      (Iff.of_eq (congrArg (fun τ => a = τ) τχ))).trans (cons₀ a).symm))
  have hτ := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) _).mp ((Formula.satisfies_isLimitOrdinal_iff ..).mp limit)
  have rankX := (context.rank_l (ZF.modelsKP hZF) source.transitive source.code).of_rank_l source.transitive context.member (χ.bound 5).property rank₁
  have hBX := source.transitive C context.member (χ.bound 5).val (χ.bound 5).property
  have hκτ : M.mem (p 1) (χ.bound 3).val := τχ.symm ▸ ((Formula.satisfies_conj_iff ..).mp exceeds).1
  have sub := (rankX.compare_l hZF source.transitive hBX hZ rankZ
    (fun a ha => hτ.1.transitive (p 1) hκτ a (lower a ha))).1
  have member a (ha : M.mem a Z) := (cons₁ a).mpr (Or.inl (sub a ha))
  have scope : M.mem (ψ.bound 4).val (χ.bound 6).val ∧ M.mem (ψ.bound 5).val (χ.bound 6).val ∧
      M.mem (ψ.bound 6).val (χ.bound 6).val := ⟨member _ low.1, member _ low.2.1, member _ low.2.2⟩
  exact ⟨eqV, scope, tg_rigid_assemble_l (context.kernel_mem_l source.transitive source.code fs.transitive nc)
    ρ χ ψ ε (Subtype.ext (ωχ.trans hw.symm)) (Subtype.ext τχ) (Subtype.ext uχ) (Subtype.ext mχ)
    (Subtype.ext (ωψ.trans hw.symm)) (Subtype.ext lψ) (Subtype.ext nψ) (Subtype.ext eψ)
    (Subtype.ext (ωε.trans hw.symm)) (Subtype.ext nε) hi hh (Subtype.ext eqV) scope seed candidate queries reply⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际下一走法的全部节点参数留在共同低层

原实数前缀和自然数标签都是已有的有界关系图。相对极限秩层的关系闭包
把这两张图放回原字母表所在层；三个长度仍取模型自己的自然数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_context_d.issued_queries_l {ω X R μ K η C γ Z : M.Domain}
    (context : Tg_context_d I ω X R η C) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K X R)
    (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 46)
    (valid : Formula.satisfies ρ tg_issued0_m) (hw : (ρ.bound 0).val = ω)
    (hZ : M.mem Z X) (rank : Vr_d X γ Z) (limit : M.IsLimitOrdinal γ)
    (omega : M.mem ω Z) (letters : M.mem (ρ.bound 6).val Z) :
    ∃ ψ χ : Env (rt_model_l C nc) 12,
      Formula.satisfies ψ tg_query_row0_m ∧
      (∀ i : Fin 6, (ψ.bound ([0, 1, 2, 3, 4, 6].get i)).val =
        (ρ.bound ([0, 1, 27, 28, 26, 23].get i)).val) ∧
      M.mem (ψ.bound 11).val (ρ.bound 25).val ∧ (∀ i : Fin 7, M.mem (ψ.bound (i.castAdd 5)).val Z) ∧
      Formula.satisfies χ tg_candidate0_m ∧
      (∀ i : Fin 12, (χ.bound i).val =
        (ρ.bound ([25, 28, 0, 24, 27, 29, 30, 31, 32, 33, 34, 35].get i)).val) ∧
      Tg_play_d I X R C (ρ.bound 4).val (ρ.bound 3).val (ρ.bound 20).val (ψ.bound 5).val := by
  obtain ⟨c, model⟩ := source.code
  have fs := (context.read_l hZF source).1
  let J := rt_pair_l fs.transitive nc hZF.1 fs.pair
  have ext := rt_model_ext_l hZF.1 fs.transitive nc
  have state := (tg_issued_sat_l J ext ρ).mp valid
  obtain ⟨h, x, s, _, _, _, r, m, b, q, f, endt, digits, rest, _, _, node, query, _, _, hk, hl, hN,
    χ, same, candidate, _⟩ := tg_issued_query_l J ext ρ valid
  have fn {a b f : (rt_model_l C nc).Domain} (h : Fn0_d a b f) : Fn0_d a.val b.val f.val := by
    let ε : Env (rt_model_l C nc) 3 := ⟨fun i => [a, b, f].get i, fun _ => a⟩
    exact (fn0_sat_l hZF.1 _ (.bound 0) (.bound 1) (.bound 2)).mp
      ((rt_model_delta_l fs.transitive nc (fn0_delta_l (.bound 0) (.bound 1) (.bound 2)) ε).mp
        ((fn0_sat_l ext ε (.bound 0) (.bound 1) (.bound 2)).mpr h))
  have fx := fn digits.1
  have ft := fn state.labels
  have play : Tg_play_d I X R C (ρ.bound 4).val (ρ.bound 3).val (ρ.bound 20).val s.val := by
    apply (tg_play_read_l I hZF.1 model source.transitive context.member fs.transitive nc J (ρ.bound 4) (ρ.bound 3) (ρ.bound 20) s).mpr
    intro i v hi
    have entry := ((rest.2 i v).mp hi).2
    exact ((digits.2 i v (digits.1.bound_l entry).1).mp entry).end_l endt
  have rest := (rt_restriction_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) fs.transitive nc fs.pair s x (ρ.bound 26)).mp rest
  have trans := rank.transitive_l source.transitive hZ
  have natural (v : (rt_model_l C nc).Domain) (hv : (rt_model_l C nc).mem v (ρ.bound 0)) : M.mem v.val Z :=
    trans ω omega v.val (hw ▸ hv)
  have hs := rank.relation_mem_l source.transitive hZ limit omega letters
    (source.transitive C context.member s.val s.property) (by
      intro p hp
      obtain ⟨i, v, pair⟩ := rest.1 p hp
      have entry := ((rest.2 i v).mp ⟨p, pair, hp⟩).2
      have bound := fx.bound_l entry
      exact ⟨i, source.omega.transitive (ZF.modelsKP hZF) _ (hw ▸ state.round) i bound.1, v, bound.2, pair⟩)
  have ht := rank.relation_mem_l source.transitive hZ limit omega omega
    (source.transitive C context.member (ρ.bound 23).val (ρ.bound 23).property) (by
      intro p hp
      obtain ⟨i, hi, v, hv, pair⟩ := ft.1 p hp
      exact ⟨i, source.omega.transitive (ZF.modelsKP hZF) _ (hw ▸ hk) i hi, v, hw ▸ hv, pair⟩)
  have control := state.control
  simp only [tg_control0_m, Formula.satisfies_conj_iff] at control
  have rules := control.2.2.1
  simp only [tg_rules_m, Formula.satisfies_conj_iff, Formula.satisfies_isEmpty_iff] at rules
  have he : ∀ x, ¬ M.mem x (ρ.bound 1).val := fun x hx =>
    rules.2.1 ⟨x, fs.transitive _ (ρ.bound 1).property x hx⟩ hx
  have heω := num_mem_l hZF.1 source.omega (show Num_d 0 (ρ.bound 1).val from he)
  let ψ : Env (rt_model_l C nc) 12 := ⟨fun i => [ρ.bound 0, ρ.bound 1, ρ.bound 27, ρ.bound 28,
    ρ.bound 26, s, ρ.bound 23, r, m, b, q, f].get i, ρ.free⟩
  refine ⟨ψ, χ, query, ?_, node, ?_, candidate, ?_, play⟩
  · intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (fun j => Fin.elim0 j)))))) i
  · intro i
    exact Fin.cases (hw.symm ▸ omega) (Fin.cases (trans ω omega _ heω) (Fin.cases (natural _ hl)
      (Fin.cases (natural _ hN) (Fin.cases (natural _ hk) (Fin.cases hs (Fin.cases ht (fun j => Fin.elim0 j))))))) i
  · intro i
    exact Fin.cases (congrArg Subtype.val (same 0)) (Fin.cases (congrArg Subtype.val (same 1))
      (Fin.cases (congrArg Subtype.val (same 2)) (Fin.cases (congrArg Subtype.val (same 3))
        (Fin.cases (congrArg Subtype.val (same 4)) (Fin.cases (congrArg Subtype.val (same 5))
          (Fin.cases (congrArg Subtype.val (same 6)) (Fin.cases (congrArg Subtype.val (same 7))
            (Fin.cases (congrArg Subtype.val (same 8)) (Fin.cases (congrArg Subtype.val (same 9))
              (Fin.cases (congrArg Subtype.val (same 10)) (Fin.cases (congrArg Subtype.val (same 11))
                (fun j => Fin.elim0 j)))))))))))) i

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 全部存档的实数前缀保持在同一原历史中

每行从保存时的原关系恢复前缀，前缀与历史的对应则在当前关系中解释。
沿初等图只搬运当前真值；实际低层固定保证存档中的前缀仍是同一对象。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

variable (I : kpair_convention_l.Interpretation M)

def Tg_saved_play_d (Y R ω V q Z B T C c b h : M.Domain) : Prop :=
  ∃ v : Fin 54 → M.Domain, Tg_saved_code_d Y R ω V q v ∧ M.mem (v 40) Z ∧ Tg_play_d I B T C c b h (v 40)

def tg_saved_play0_m : Formula 1 12 := rt_exists_m 54 (.conj
  (tg_saved_code_m (.bound 54) (.bound 55) (.bound 56) (.bound 57) (.bound 58)
    (fun i : Fin 54 => .bound (i.castAdd 12)))
  (.conj (.mem (.bound 40) (.bound 59))
    (tg_play_m (.bound 60) (.bound 61) (.bound 62) (.bound 63) (.bound 64) (.bound 65) (.bound 40))))

theorem tg_saved_play0_closed_l : tg_saved_play0_m.FreeClosed := by
  apply (rt_exists_closed_l _).mpr
  refine ⟨tg_saved_code_closed_l _ _ _ _ _ _ rfl rfl rfl rfl rfl (fun _ => rfl), ?_⟩
  exact ⟨⟨rfl, rfl⟩, tg_play_closed_l _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl⟩

theorem tg_saved_play0_sat_l (ρ : Env M 12) : Formula.satisfies ρ tg_saved_play0_m ↔
    Tg_saved_play_d I (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) (ρ.bound 3) (ρ.bound 4) (ρ.bound 5)
      (ρ.bound 6) (ρ.bound 7) (ρ.bound 8) (ρ.bound 9) (ρ.bound 10) (ρ.bound 11) := by
  rw [tg_saved_play0_m, rt_exists_sat_l]
  apply exists_congr
  intro v
  simp only [Formula.satisfies_conj_iff, tg_saved_code_sat_l, tg_play_sat_l I, Formula.satisfies_mem_iff, Term.eval_bound]
  have tuple : (fun j : Fin 54 => (rt_push_d ρ 54 v).bound (j.castAdd 12)) = v := funext (rt_push_new_l ρ v)
  rw [tuple]
  rw [
    show (rt_push_d ρ 54 v).bound 54 = ρ.bound 0 from rt_push_old_l ρ v 0,
      show (rt_push_d ρ 54 v).bound 55 = ρ.bound 1 from rt_push_old_l ρ v 1,
      show (rt_push_d ρ 54 v).bound 56 = ρ.bound 2 from rt_push_old_l ρ v 2,
      show (rt_push_d ρ 54 v).bound 57 = ρ.bound 3 from rt_push_old_l ρ v 3,
      show (rt_push_d ρ 54 v).bound 58 = ρ.bound 4 from rt_push_old_l ρ v 4,
      show (rt_push_d ρ 54 v).bound 59 = ρ.bound 5 from rt_push_old_l ρ v 5,
      show (rt_push_d ρ 54 v).bound 60 = ρ.bound 6 from rt_push_old_l ρ v 6,
      show (rt_push_d ρ 54 v).bound 61 = ρ.bound 7 from rt_push_old_l ρ v 7,
      show (rt_push_d ρ 54 v).bound 62 = ρ.bound 8 from rt_push_old_l ρ v 8,
      show (rt_push_d ρ 54 v).bound 63 = ρ.bound 9 from rt_push_old_l ρ v 9,
      show (rt_push_d ρ 54 v).bound 64 = ρ.bound 10 from rt_push_old_l ρ v 10,
      show (rt_push_d ρ 54 v).bound 65 = ρ.bound 11 from rt_push_old_l ρ v 11]
  rfl

def tg_saved_play_m {d} (Y R ω V q Z B T C c b h : Term d) : Formula 1 d :=
  tg_saved_play0_m.bind (fun i => [Y,R,ω,V,q,Z,B,T,C,c,b,h].get i)

@[simp] theorem tg_saved_play_closed_l {d} (Y R ω V q Z B T C c b h : Term d)
    (hY : Y.freeSupport = []) (hR : R.freeSupport = []) (hω : ω.freeSupport = []) (hV : V.freeSupport = [])
    (hq : q.freeSupport = []) (hZ : Z.freeSupport = []) (hB : B.freeSupport = []) (hT : T.freeSupport = [])
    (hC : C.freeSupport = []) (hc : c.freeSupport = []) (hb : b.freeSupport = []) (hh : h.freeSupport = []) :
    (tg_saved_play_m Y R ω V q Z B T C c b h).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _
    (Fin.cases hY (Fin.cases hR (Fin.cases hω (Fin.cases hV (Fin.cases hq (Fin.cases hZ (Fin.cases hB (Fin.cases hT (Fin.cases hC (Fin.cases hc (Fin.cases hb (Fin.cases hh (fun i => Fin.elim0 i))))))))))))) _).mpr tg_saved_play0_closed_l

theorem tg_saved_play_sat_l {d} (ρ : Env M d) (Y R ω V q Z B T C c b h : Term d) :
    Formula.satisfies ρ (tg_saved_play_m Y R ω V q Z B T C c b h) ↔
      Tg_saved_play_d I (Y.eval ρ) (R.eval ρ) (ω.eval ρ) (V.eval ρ) (q.eval ρ) (Z.eval ρ)
        (B.eval ρ) (T.eval ρ) (C.eval ρ) (c.eval ρ) (b.eval ρ) (h.eval ρ) := by
  rw [tg_saved_play_m, Formula.satisfies_bind, tg_saved_play0_sat_l I]
  rfl

def Tg_past_play_d (ω H Z B T C c b h : M.Domain) : Prop := ∀ m i Y R μ K η D L V q,
  Tg_past_at_d H m i Y R μ K η D L V q → Tg_saved_play_d I Y R ω V q Z B T C c b h

def tg_past_play_m {d} (ω H Z B T C c b h : Term d) : Formula 1 d := set[d] ⟪∀ m i Y R μ K η D L V q,
  ⌜tg_past_at_m⌝ₚ(⌜H⌝ₛ,m,i,Y,R,μ,K,η,D,L,V,q) →
    ⌜tg_saved_play_m⌝ₚ(Y,R,⌜ω⌝ₛ,V,q,⌜Z⌝ₛ,⌜B⌝ₛ,⌜T⌝ₛ,⌜C⌝ₛ,⌜c⌝ₛ,⌜b⌝ₛ,⌜h⌝ₛ)⟫
derive_free_closed tg_past_play_m

theorem tg_past_play_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω H Z B T C c b h : Term d) :
    Formula.satisfies ρ (tg_past_play_m ω H Z B T C c b h) ↔
      Tg_past_play_d I (ω.eval ρ) (H.eval ρ) (Z.eval ρ) (B.eval ρ) (T.eval ρ)
        (C.eval ρ) (c.eval ρ) (b.eval ρ) (h.eval ρ) := by
  simp only [tg_past_play_m, Tg_past_play_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    tg_past_at_sat_l hE, tg_saved_play_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem tg_past_play_empty_l {ω H Z B T C c b h : M.Domain} (empty : ∀ x, ¬ M.mem x H) : Tg_past_play_d I ω H Z B T C c b h :=
  fun _ _ _ _ _ _ _ _ _ _ _ ⟨_, ⟨p, _, hp⟩, _⟩ => (empty p hp).elim

theorem Tg_past_play_d.mono_l (hE : Extensional M) {a ω H Z B T C : M.Domain} (model : Smem_d I a B T)
    (bt : M.TransitiveSet B) (hC : M.mem C B) (ct : M.TransitiveSet C) (nc : Nonempty {x // M.mem x C})
    (J : kpair_convention_l.Interpretation (rt_model_l C nc)) (c b h h' : (rt_model_l C nc).Domain)
    (play : Tg_past_play_d I ω H Z B T C c.val b.val h.val) (sub : M.MemberSubset h.val h'.val) :
    Tg_past_play_d I ω H Z B T C c.val b.val h'.val := by
  intro m i Y R μ K η D L V q row
  obtain ⟨v, code, low, play⟩ := play m i Y R μ K η D L V q row
  exact ⟨v, code, low, play.mono_l I hE model bt hC ct nc J c b h h' sub⟩

theorem Tg_past_play_d.map_l (hZF : M.Models ZF) {ω H Z X R d Y S e j C C' c c' b b' h h' : M.Domain}
    (hw : M.IsOmega ω) (mx : Smdl_d I d X R) (my : Smdl_d I e Y S) (map : Smap_d I ω d e X Y j)
    (iC : M.PairMember I C C' j) (ic : M.PairMember I c c' j) (ib : M.PairMember I b b' j) (ih : M.PairMember I h h' j)
    (fixed : ∀ s, M.mem s Z → M.PairMember I s s j) (play : Tg_past_play_d I ω H Z X R C c b h) :
    Tg_past_play_d I ω H Z Y S C' c' b' h' := by
  intro m i U T μ K η D L V q row
  obtain ⟨v, code, low, play⟩ := play m i U T μ K η D L V q row
  exact ⟨v, code, low, play.map_l I hZF hw mx my map iC ic ib ih (fixed _ low)⟩

theorem Tg_past_play_d.push_l (hZF : M.Models ZF) {ω n H n' H' X T b Z C c d h i Y R μ K η D L V q : M.Domain}
    (updated : Tg_past_d hZF ω n' H' X b) (succ : M.SuccessorOf n' n)
    (newest : Tg_past_at_d H' n i Y R μ K η D L V q)
    (entries : ∀ m r, M.mem m n → (Rd_entry_d m r H' ↔ Rd_entry_d m r H))
    (play : Tg_past_play_d I ω H Z X T C c d h) (v : Fin 54 → M.Domain) (code : Tg_saved_code_d Y R ω V q v)
    (low : M.mem (v 40) Z) (trace : Tg_play_d I X T C c d h (v 40)) : Tg_past_play_d I ω H' Z X T C c d h := by
  intro m i₀ Y₀ R₀ μ₀ K₀ η₀ D₀ L₀ V₀ q₀ row
  obtain ⟨r, hr, cell⟩ := row
  rcases (succ m).mp ((updated.sequence.2.2 m).mpr ⟨r, hr⟩) with lt | eq
  · exact play m i₀ Y₀ R₀ μ₀ K₀ η₀ D₀ L₀ V₀ q₀ ⟨r, (entries m r lt).mp hr, cell⟩
  · have eq := hZF.1.eq_of_same_members m n eq
    subst m
    obtain ⟨s, hs, pack⟩ := newest
    have eq := updated.sequence.2.1.2 n r s hr hs
    subst s
    have eq := rt_tuple_inj_l cell pack
    have eY : Y₀ = Y := congrFun eq 1
    have eR : R₀ = R := congrFun eq 2
    have eV : V₀ = V := congrFun eq 8
    have eq : q₀ = q := congrFun eq 9
    subst Y₀ R₀ V₀ q₀
    exact ⟨v, code, low, trace⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 两种实际树后继共用的完整回答证书

第一边产生回答所在的奇数模型，第二边从原偶数模型出发。保留原请求的
字面对应、两个根图、共同层、奇数边的图恢复以及同一次历史追加。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_tree_step_d (ω X R₀ η c₀ α ξ T J G E c o Cᵣ γ Z H : M.Domain)
    {C : M.Domain} (nc : Nonempty {x // M.mem x C}) (ι : Env (rt_model_l C nc) 46) : Prop :=
  ∃ k β T₁ J₁ G₁ E₁ H₁ a Y R μ K η₁ C₁ π₁,
    It_pnice_d hZF ω c₀ β T₁ J₁ G₁ E₁ H₁ ∧ It_extension_d α ξ k T J G E β T₁ J₁ G₁ E₁ ∧
    Rd_entry_d α a J₁ ∧ Smem_d I a Y R ∧ Ic_model_d hZF ω μ K Y R ∧ Tg_context_d I ω Y R η₁ C₁ ∧
    It_map_d G₁ o α π₁ ∧ Rd_entry_d Cᵣ C₁ π₁ ∧ Tg_anchor_d I γ Z Y R π₁ ∧
    (∀ p κ L F, Rd_entry_d ξ p E₁ → It_payload_d p κ L F →
      ∃ c X R, Rd_entry_d ξ c J₁ ∧ Smdl_d I c X R ∧ It_lower_d I γ X R κ) ∧
    ∃ n₁ : Nonempty {x // M.mem x C₁}, ∃ ρ : Env (rt_model_l C₁ n₁) 54,
      let q := fun i => (ρ.bound i).val
      let σ := Fin.cases (q 47) (Fin.cases (q 48) (Fin.cases (q 49)
        (Fin.cases (q 50) (Fin.cases (q 51) (Fin.cases (q 52) (fun _ => q 53))))))
      Formula.satisfies ρ tg_round0_m ∧ Tg_request_d Eq (fun i => (ι.bound i).val) q ∧ M.MemberSubset γ (q 15) ∧
      Tg_odd_d ω H ξ α k G₁ (ι.bound 1).val (ι.bound 23).val (ι.bound 22).val (ι.bound 7).val (q 19) (q 22) (q 40) (q 42) ∧
      (M.mem (q 40) Z ∧ Tg_play_d I X R₀ C (ι.bound 4).val (ι.bound 3).val (ι.bound 20).val (q 40)) ∧
      ∃ β₂ T₂ J₂ G₂ E₂ H₂ d j N R₂ K₂ L F κ U D u η₂ C₂ W π₂,
        It_pnice_d hZF ω c₀ β₂ T₂ J₂ G₂ E₂ H₂ ∧ It_extension_d β α ξ T₁ J₁ G₁ E₁ β₂ T₂ J₂ G₂ E₂ ∧
        Rd_entry_d β d J₂ ∧ It_map_d G₂ ξ β j ∧ Smem_d I d N R₂ ∧ Ic_model_d hZF ω L K₂ N R₂ ∧
        It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω (ι.bound 24).val L F c d j ∧ Wd_crit_d I X j (ι.bound 24).val κ ∧
        (∃ p, Rd_entry_d α p E₂ ∧ It_payload_d p (ι.bound 24).val L F) ∧
        M.IsLimitOrdinal L ∧ M.mem (q 15) L ∧ M.MemberSubset L κ ∧
        (∀ i ν, Rd_entry_d i ν H₂ → M.mem ν κ ∨ ν = κ) ∧
        Rd_entry_d (ι.bound 30).val U j ∧ Rd_entry_d (ι.bound 31).val D j ∧ Rd_entry_d (ι.bound 25).val u j ∧
        Tg_reply_d I ω (q 23) (q 24) κ (q 15) U D (q 12) u (q 11) (q 36) σ (q 38) ⟨q 2, q 1, q 0⟩ ∧
        Rd_entry_d η η₂ j ∧ Rd_entry_d C C₂ j ∧ Tg_context_d I ω N R₂ η₂ C₂ ∧
        M.mem W Y ∧ Vr_d Y L W ∧ Er_level_d N L W ∧
        It_map_d G₂ o β π₂ ∧ Rd_entry_d Cᵣ C₂ π₂ ∧ Tg_anchor_d I γ Z N R₂ π₂ ∧
        Tg_past_update_d hZF ω X (ι.bound 24).val α Y R μ K η₁ C₁ L W N κ j J J₂ q

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 继续较早轮的实际跨模型超幂

当前模型中的弹性和超过见证产生 E₂ₙ，施加源是所选较早节点的完整模型。
共同秩段识别旧类型的像，原程序沿实际树根图进入目标；由原子类型查询
自动取得候选的较低层实现。旧回答基底先推出最大序数查询，再在同一目标
反射层恢复恰好一个新标签，并直接形成下一轮输入、回答及实际奇数树边。
当前节点查询和候选由原策略已经发出的走法自动读取，低层参数界由原字母表
所在层推出。旧轮记录、dcp 弹性及任意排列均保留；同一扩展器的支撑严格超过输入的历史界。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω X η C : M.Domain} (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 29)
local notation "p" => (fun i => Subtype.val (Env.bound ρ i))
local notation "σ" => (Fin.cases (p 21) (Fin.cases (p 22) (Fin.cases (p 23) (Fin.cases (p 24)
  (Fin.cases (p 25) (Fin.cases (p 26) (fun _ => p 27)))))))

theorem Tg_context_d.continue_image_tree_l {c₀ α ξ T J G E H k c d R Y S K K' ζ V η₀ C₀ o π π₀ Cᵣ γ Z₀
    H₀ μᵣ Kₕ Lᵣ Vᵣ qᵣ : M.Domain}
    (context : Tg_context_d I ω X R η C) (prior : Tg_context_d I ω Y S η₀ C₀)
    (nc₀ : Nonempty {x // M.mem x C₀}) (ρ₀ : Env (rt_model_l C₀ nc₀) 54)
    (old : Formula.satisfies ρ₀ tg_round0_m) (oldType : (ρ₀.bound 11).val = p 7)
    (oldκ : (ρ₀.bound 15).val = p 1) (oldn : (ρ₀.bound 24).val = p 3) (oldU : (ρ₀.bound 13).val = p 5)
    (owner : Ic_model_d hZF ω (p 1) K X R) (source : Ic_model_d hZF ω (p 1) K' Y S)
    (tree : It_pnice_d hZF ω c₀ α T J G E H) (succ : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c J) (hd : Rd_entry_d k d J) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (ho : ∀ x, ¬ M.mem x o) (root : It_map_d G o ξ π) (root₀ : It_map_d G o k π₀)
    (iRoot : Rd_entry_d Cᵣ C π) (iRoot₀ : Rd_entry_d Cᵣ C₀ π₀)
    (anchor : Tg_anchor_d I γ Z₀ X R π) (priorAnchor : Tg_anchor_d I γ Z₀ Y S π₀) (lower : M.MemberSubset γ (p 1))
    (hγ : M.IsLimitOrdinal γ) (hωZ : M.mem ω Z₀)
    (ι : Env (rt_model_l C nc) 46) (issued : Formula.satisfies ι tg_issued0_m)
    (ne : ι.bound 23 ≠ ι.bound 1)
    (row : Tg_past_at_d H₀ (ι.bound 22).val k Y S μᵣ Kₕ η₀ C₀ Lᵣ Vᵣ qᵣ)
    (code : Tg_saved_code_d Y S ω Vᵣ qᵣ (fun i => (ρ₀.bound i).val))
    (lowS : M.mem (ρ₀.bound 40).val Z₀)
    (oldPlayed : Tg_play_d I X R C (ι.bound 4).val (ι.bound 3).val (ι.bound 20).val (ρ₀.bound 40).val)
    (labelSub : M.MemberSubset (ρ₀.bound 41).val (ι.bound 23).val)
    (links : ∀ i : Fin 6, (ι.bound ([0, 1, 27, 28, 24, 25].get i)).val =
      [ω, (ρ₀.bound 17).val, p 3, p 9, p 8, p 13].get i)
    (codes : ∀ i : Fin 9, p ([14, 16, 21, 22, 23, 24, 25, 26, 27].get i) =
      (ι.bound ([36, 37, 38, 39, 40, 41, 42, 43, 44].get i)).val)
    (letters : M.mem (ι.bound 6).val Z₀)
    (hw : p 0 = ω) (hδ : M.IsLimitOrdinal (p 2)) (regular : Sc_regular_d X (p 2))
    (hV : M.mem V X) (rank : Vr_d X ζ V)
    (hV' : M.mem V Y) (rank' : Vr_d Y ζ V) (hζ : M.IsLimitOrdinal ζ)
    (hVC : M.mem V C₀) (hζδ : M.mem ζ (p 2)) (hκV : M.mem (p 1) V)
    (hU : M.mem (p 5) V) (hD : M.mem (p 6) V) (hu : M.mem (p 7) V)
    (above : ∀ i μ, Rd_entry_d i μ H → M.mem μ (p 28) ∨ μ = p 28)
    (seed : Formula.satisfies ρ tc_seed0_m) :
    Tg_tree_step_d hZF ω X R η c₀ α ξ T J G E c o Cᵣ γ Z₀ H₀ nc ι := by
  obtain ⟨ag, az, ar, af⟩ := anchor.read_l (ZF.modelsKP hZF) owner.source.transitive mx
  obtain ⟨_, pz, pr, pf⟩ := priorAnchor.read_l (ZF.modelsKP hZF) source.source.transitive my
  obtain ⟨ψ, χ, queries, eqψ, node, queryLow, candidate, eqχ, played⟩ :=
    context.issued_queries_l hZF owner.source nc ι issued (links 0) az ar hγ hωZ letters
  have queryRequest := eqψ
  have candidateRequest := eqχ
  have ωψ : (ψ.bound 0).val = ω := (eqψ 0).trans (links 0)
  have eψ : (ψ.bound 1).val = (ρ₀.bound 17).val := (eqψ 1).trans (links 1)
  have lψ : (ψ.bound 2).val = p 3 := (eqψ 2).trans (links 2)
  have nψ : (ψ.bound 3).val = p 9 := (eqψ 3).trans (links 3)
  have node : M.mem (ψ.bound 11).val (p 13) := (show (ι.bound 25).val = p 13 from links 5) ▸ node
  have ωχ : (χ.bound 2).val = ω := (eqχ 2).trans (links 0)
  have τχ : (χ.bound 3).val = p 8 := (eqχ 3).trans (links 4)
  have uχ : (χ.bound 0).val = p 13 := (eqχ 0).trans (links 5)
  have mχ : (χ.bound 1).val = p 9 := (eqχ 1).trans (links 3)
  have fs := (context.read_l hZF owner.source).1
  have facts := seed
  simp only [tc_seed0_m, Formula.satisfies_conj_iff] at facts
  let fp : Fin 12 → Term 29 := fun i => [.bound 0, .bound 3, .bound 14, .bound 15, .bound 16,
    .bound 21, .bound 22, .bound 23, .bound 24, .bound 25, .bound 26, .bound 27].get i
  let ρp := Definitional.Env.substitute ρ fp
  have program : Formula.satisfies ρp ts_program0_m := (Formula.satisfies_bind ρ fp ts_program0_m).mp facts.2.1
  have prog := program
  simp only [ts_program0_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at prog
  have hb : M.mem (p 14) ω := hw ▸ prog.2.1
  have valid := (context.kernel_mem_l owner.source.transitive owner.source.code (context.read_l hZF owner.source).1.transitive nc).continue_l ρ seed
  simp only [tc_result0_m, tc_image_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff] at valid
  obtain ⟨⟨A, K₁, R₁, L, F, a, a', B, S₁, f, κ', U', D', u', core, hχL, _, subtype⟩, _, _⟩ := valid
  have hχL : M.mem (p 28) L.val := (Formula.satisfies_mem_iff ..).mp hχL
  let ε := ρ.push A |>.push K₁ |>.push R₁ |>.push L |>.push F |>.push a |>.push a' |>.push B
    |>.push S₁ |>.push f |>.push κ' |>.push U' |>.push D' |>.push u'
  let q (t : Term 29) := t.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  let t (i : Fin 14) : Term 43 := .bound ⟨i.val, by omega⟩
  obtain ⟨_, pₛ, _, _⟩ := owner.read_l hZF
  obtain ⟨hA, cut, K₂, small, _, hκL, hτL, loc, card, strong, ma, mb, smallUltra, crit, _, _, iU, iD, iu⟩ :=
    ti_image_read_l hZFC nc ε (q (.bound 0)) (q (.bound 1)) (q (.bound 2)) (q (.bound 8))
      (q (.bound 5)) (q (.bound 6)) (q (.bound 7))
      (t 13) (t 12) (t 11) (t 10) (t 9) (t 8) (t 7) (t 6) (t 5) (t 4) (t 3) (t 2) (t 1) (t 0)
      owner.source pₛ context.member (context.rank_l (ZF.modelsKP hZF) owner.source.transitive owner.source.code) fs (by exact hw) (by exact hδ) (by exact regular) core
  have subtype := ts_subtype_source_l (ZF.modelsKP hZF) fs.transitive nc _ _ _ _ _ _ _ _ _ _ _ _ subtype
  simp only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest] at subtype
  have slots : (fun i : Fin 7 => (Definitional.Term.eval ε
      (Fin.cases (q (.bound 21)) (Fin.cases (q (.bound 22)) (Fin.cases (q (.bound 23))
        (Fin.cases (q (.bound 24)) (Fin.cases (q (.bound 25)) (Fin.cases (q (.bound 26))
          (fun _ => q (.bound 27))))))) i)).val) = σ := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  have subtype' : Ts_subtype_d ω (p 3) κ'.val (p 8) (p 9) U'.val (p 13) (p 14) σ (p 16) u'.val :=
    slots ▸ (hw ▸ subtype)
  have hL := (loc.ordinals_l (ZF.modelsKP hZF) small.transitive small.code).2
  obtain ⟨β, T', J', G', E', H', d', j, N, R', K₀, W, κ₀, next, ext, target, edge, mn, ready,
    ultra, critical, bound, payload, heights, hW, common, level, agreement, same, fixed⟩ :=
    it_working_image_l hZFC tree succ hc hd mx my owner source hA cut hδ small ma mb smallUltra loc strong card
      hκL hV rank hV' rank' hζ hζδ hκV (fun i μ hm =>
        (above i μ hm).elim (hL.transitive (p 28) hχL μ) (fun eq => eq.symm ▸ hχL))
  have eq := (ultra.elementary_l hZF my.1 mn.1).1.1.1.2 (p 1) κ₀ κ'.val critical.image (same _ _ hκV crit.image)
  subst κ₀
  have hj := ultra.elementary_l hZF my.1 mn.1
  obtain ⟨η', C', iη, iC, context'⟩ := prior.map_l hZF source.source.omega my.1 mn.1 hj
    (hj.omega_l I hZF source.source.omega source.source.transitive ready.source.transitive my mn source.source.omega_mem)
  let nv : Nonempty {x // M.mem x C'} := ⟨⟨ω, (context'.omega_l ready.source.code)⟩⟩
  obtain ⟨kC, layerC, idC⟩ := rr_layer_mem_l I hZF my source.source.transitive prior.member
    (prior.read_l hZF source.source).1.transitive
  obtain ⟨kD, layerD, idD⟩ := rr_layer_mem_l I hZF mn ready.source.transitive context'.member
    (context'.read_l hZF ready.source).1.transitive
  obtain ⟨θ, trace, moved⟩ := hj.relative_image_l hZF source.source.omega my.1 mn.1
    layerC layerD nc₀ nv iC tg_round0_m tg_round0_closed_l ρ₀
  have images i : Rd_entry_d (ρ₀.bound i).val (θ.bound i).val j := by
    obtain ⟨a, b, ha, edge, hb⟩ := trace i
    exact ((idC _ _).mp ha).2.symm ▸ ((idD _ _).mp hb).2.symm ▸ edge
  have oldImage : Rd_entry_d (p 7) (θ.bound 11).val j := oldType ▸ images 11
  have oldEq := hj.1.1.1.2 (p 7) (θ.bound 11).val u'.val oldImage (same _ _ hu iu)
  have inner x (hx : M.mem x V) := (prior.read_l hZF source.source).1.transitive V hVC x hx
  have inU := (hj.member_l I hZF source.source.omega my mn (same _ _ hU iU) iC).mp (inner _ hU)
  have inD := (hj.member_l I hZF source.source.omega my mn (same _ _ hD iD) iC).mp (inner _ hD)
  have inu := (hj.member_l I hZF source.source.omega my mn (same _ _ hu iu) iC).mp (inner _ hu)
  have relativeSubtype := context'.subtype_l hZF ready.source inU inu hb subtype'
  have data := subtype'
  obtain ⟨_, _, _, query, _⟩ := data
  have inw := (context'.read_l hZF ready.source).1.transitive U'.val inU (p 13) query.1.1
  -- 新语言沿实际树根图传递；共同秩层同时给出所有名字及查询的目标成员性。
  obtain ⟨B₀, R₀, wᵣ, Kᵣ, zᵣ, mb, rootSource, numbers⟩ := (tree.tree.sources o c₀ (tree.tree.root o ho)).objects
  have jRoot := tree.tree.diagram.elementary o ξ π c₀ B₀ R₀ c X R root (tree.tree.root o ho) hc mb mx.1
  have jPrior := tree.tree.diagram.elementary o k π₀ c₀ B₀ R₀ d Y S root₀ (tree.tree.root o ho) hd mb my.1
  -- 旧回答基底由实际较早轮读取，再沿同一根图送到当前层。
  have fs₀ := (prior.read_l hZF source.source).1
  obtain ⟨oldSeed, oldRound⟩ := (Formula.satisfies_conj_iff ..).mp old
  simp only [tg_seed0_m, Formula.satisfies_rename, tg_seed_m, Formula.satisfies_conj_iff] at oldSeed
  have omega₀ := (Formula.satisfies_isOmega_iff ..).mp oldSeed.1
  let w₀ : (rt_model_l C₀ nc₀).Domain := ⟨ω, (prior.omega_l source.source.code)⟩
  have actualω := rt_omega_l fs₀.transitive nc₀ hZF.1 w₀ source.source.omega
  have eqω := (rt_model_ext_l hZF.1 fs₀.transitive nc₀).eq_of_same_members (ρ₀.bound 16) w₀
    (fun x => ⟨omega₀.2 w₀ actualω.1 x, actualω.2 (ρ₀.bound 16) omega₀.1 x⟩)
  have ω₀ : (ρ₀.bound 16).val = ω := congrArg Subtype.val eqω
  have heω : M.mem (ρ₀.bound 17).val ω := ω₀ ▸ oldSeed.2.2.1
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff] at oldRound
  obtain ⟨_, _, _, _, _, _, _, _, _, replyLanguage, _, _, heightMember, _⟩ := oldRound
  simp only [tg_reply_language_m, Formula.satisfies_bind, tg_reply_language0_m,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at replyLanguage
  obtain ⟨finite₀, _, last₀, _, _, _, _, _, _, _, base₀⟩ := replyLanguage
  let f : Fin 7 → Term 54 := fun i => [.bound 16, .bound 17, .bound 23, .bound 24, .bound 2, .bound 1, .bound 0].get i
  let ε₀ := Definitional.Env.substitute ρ₀ f
  -- 只比较七个参数，避免为核对两次代入而展开整条查询公式。
  simp only [tg_reply_base_m, Formula.satisfies_bind] at base₀
  have base₀ : Formula.satisfies ε₀ tg_reply_base0_m := by
    apply (Formula.closed_env_l tg_reply_base0_m tg_reply_base0_closed_l (ρ := _) (η := ε₀) ?_).mp base₀
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun a => Fin.elim0 a))))))) i
  have zt := pr.transitive_l source.source.transitive pz
  have hwZ : M.mem ω Z₀ := ωψ ▸ queryLow 0
  have hnω : M.mem (ρ₀.bound 24).val ω := ω₀ ▸ finite₀
  have low₀ : ∀ i : Fin 4, M.mem (ε₀.bound (i.castAdd 3)).val Z₀ := by
    intro i
    exact Fin.cases (ω₀.symm ▸ hwZ) (Fin.cases (zt _ hwZ _ heω)
      (Fin.cases (zt _ hwZ _ (source.source.omega.transitive (ZF.modelsKP hZF) _ hnω _ last₀))
        (Fin.cases (zt _ hwZ _ hnω) (fun j => Fin.elim0 j)))) i
  obtain ⟨_, ε', eqε, reply'⟩ := priorAnchor.reply_peer_l hZF nc₀ ε₀ anchor nc source.source prior.member fs₀
    owner.source.transitive fs.transitive mb my mx jPrior jRoot iRoot₀ iRoot hγ ω₀ low₀ base₀
  have qShape := (Formula.satisfies_conj_iff ..).mp queries |>.2
  have sn := (rt_successor_l fs.transitive nc hZF.1 (ψ.bound 3) (ψ.bound 2)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp qShape.2)
  have cElastic := (Formula.satisfies_conj_iff ..).mp candidate |>.2
  simp only [tg_elastic_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff] at cElastic
  obtain ⟨v, drop, _⟩ := cElastic
  have drop := (td_dcp_source_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) fs.transitive nc fs.pair
    (χ.push v) (.bound 5) (.bound 2) (.bound 8) (.bound 1) (.bound 0)).mp drop
  have mω : M.mem (p 9) ω := hw ▸ ((Formula.satisfies_conj_iff ..).mp ((context.kernel_mem_l owner.source.transitive owner.source.code (context.read_l hZF owner.source).1.transitive nc).continue_l ρ seed)).2.1
  have ℓχ : (ψ.bound 2).val = (χ.bound 4).val := sn.predecessor_eq hZF.1
    ((owner.source.omega.members_areOrdinals (ZF.modelsKP hZF) _ (nψ.symm ▸ mω)).mem sn.predecessor_mem)
    (Eq.mp (congrArg (fun a => M.SuccessorOf a (χ.bound 4).val) (mχ.trans nψ.symm)) drop.1)
  obtain ⟨_, scope, maximum⟩ := context.rigid_l hZF nc ρ χ ψ ε' owner.source az ar lower
    ⟨queryLow 4, queryLow 5, queryLow 6⟩ hw ωχ τχ uχ mχ ωψ ℓχ nψ (eψ.trans (eqε 1).symm)
    ((eqε 0).trans ω₀) ((eqε 3).trans oldn)
    (Eq.mpr ((congrArg (fun a => M.mem a (p 3)) (eqε 2)).trans
      (congrArg (fun a => M.mem (ρ₀.bound 23).val a) oldn.symm)) last₀)
    (Eq.mpr (congrArg (fun a => M.mem a (p 7)) (eqε 6)) (oldType ▸ heightMember)) seed candidate queries reply'
  obtain ⟨π', root'⟩ := next.tree.diagram.map_l hZF (next.tree.diagram.order.root_l hZF ho α ext.1.predecessor_mem)
  have kRoot := next.tree.diagram.elementary o α π' c₀ B₀ R₀ d' N R' root'
    (next.tree.root o ho) target mb mn.1
  have oldRoot := (ext.2.2.2.1 o k π₀ ((tree.tree.diagram.model_domain k).mpr ⟨d, hd⟩)).mpr root₀
  have iRoot' := next.tree.diagram.comp o k α π₀ j π' oldRoot edge root' Cᵣ C₀ C' iRoot₀ iC
  have hLimit := card.limit_l (ZF.modelsKP hZF) small.transitive (small.algebra_l (ZF.modelsKP hZF)).pair
  have fixedCopy := fixed
  obtain ⟨V₀, hV₀, rank₀, _, _, pointwise⟩ := fixedCopy
  have hgL := ordinal_down_l (ZF.modelsKP hZF) (ar.ordinal_l az) hLimit.1 lower hκL
  have hgW := common.ordinal_subset_l hZF owner.source.transitive hW γ hgL
  obtain ⟨hzW, rzW⟩ := common.rank_l hZF owner.source.transitive hW hLimit hgW az ar
  have sz := (rank₀.compare_l hZF source.source.transitive hV₀ pz pr lower).1
  have anchor' := Tg_anchor_d.of_mem_l hZF mn ready.source.transitive
    (ready.source.transitive W level.member γ hgW) (ready.source.transitive W level.member Z₀ hzW)
    (level.hierarchy.of_rank_l ready.source.transitive level.member hzW rzW)
    (fun x hx => next.tree.diagram.comp o k α π₀ j π' oldRoot edge root' x x x
      (pf x hx) (pointwise x (sz x hx)))
  obtain ⟨_, nz, nr, nf⟩ := anchor'.read_l (ZF.modelsKP hZF) ready.source.transitive mn
  have fixedZ z (hz : M.mem z Z₀) : Rd_entry_d z z j := by
    obtain ⟨z', _, iz⟩ := hj.1.1.2.2 z (source.source.transitive Z₀ pz z hz)
    have eq := kRoot.1.1.1.2 z z' z (next.tree.diagram.comp o k α π₀ j π' oldRoot edge root'
      z z z' (pf z hz) iz) (nf z hz)
    exact eq ▸ iz
  have lowT : M.mem (ρ₀.bound 41).val Z₀ := pr.subset_mem_l source.source.transitive
    pz (queryRequest 5 ▸ queryLow 6)
    (source.source.transitive C₀ prior.member _ (ρ₀.bound 41).property) labelSub
  obtain ⟨allQueries, ψ', eqψ, movedψ⟩ := anchor.query_peer_l hZF nc ψ anchor' nv owner.source context.member fs
    ready.source.transitive (context'.read_l hZF ready.source).1.transitive mb mx mn jRoot kRoot
    iRoot iRoot' hγ ωψ queryLow queries
  have carried := ts_program_peer_l hZF nc ρp owner.source.omega numbers rootSource.ext owner.source.transitive
    ready.source.transitive mb mx mn jRoot kRoot iRoot iRoot' fs.transitive
    (context'.read_l hZF ready.source).1.transitive (context'.omega_l ready.source.code) hw program
  have σeq : (fun i : Fin 7 => [p 21, p 22, p 23, p 24, p 25, p 26, p 27].get i) = σ := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  have program' : Ts_program_in_d ω (p 3) (p 14) (p 16) σ C' := σeq ▸ carried
  have hκC' := (hj.member_l I hZF source.source.omega my mn critical.image iC).mp (inner _ hκV)
  have hLC' := (context'.rank_l (ZF.modelsKP hZF) ready.source.transitive ready.source.code).subset_mem_l ready.source.transitive context'.member hκC' ready.source.cardinal_mem bound
  have hWC' := ((context'.rank_l (ZF.modelsKP hZF) ready.source.transitive ready.source.code).rank_l hZF ready.source.transitive context'.member (context'.limit_l (ZF.modelsKP hZF) ready.source.transitive ready.source.code)
    hLC' level.member level.hierarchy).1
  have κW := common.ordinal_subset_l hZF owner.source.transitive hW (p 1) hκL
  have ωW := common.subset_mem_l owner.source.transitive hW κW owner.source.omega_mem owner.source.below
  have τW := common.ordinal_subset_l hZF owner.source.transitive hW (p 8) hτL
  obtain ⟨hmω, low, nχ, χ', eqχ, movedχ⟩ := context.candidate_peer_l hZF nc χ context' owner.source ready.source
    numbers rootSource.ext mb mx mn jRoot kRoot iRoot iRoot'
    hW common level.member level.hierarchy hLimit
    ωW (Eq.mpr (congrArg (fun a => M.mem a W) τχ) τW) hWC' ωχ
    (Eq.mpr (congrArg (fun a => M.mem a C') uχ) inw) candidate
  have natural := hj.natural_l hZF source.source.omega source.source.transitive ready.source.transitive my mn source.source.omega_mem
  have nImage : Rd_entry_d (p 3) (θ.bound 24).val j := oldn ▸ images 24
  have κImage : Rd_entry_d (p 1) (θ.bound 15).val j := oldκ ▸ images 15
  have UImage : Rd_entry_d (p 5) (θ.bound 13).val j := oldU ▸ images 13
  have eqn := hj.1.1.1.2 (p 3) (θ.bound 24).val (p 3) nImage (natural _ (hw ▸ prog.1))
  have eqκ := hj.1.1.1.2 (p 1) (θ.bound 15).val κ'.val κImage critical.image
  have eqU := hj.1.1.1.2 (p 5) (θ.bound 13).val U'.val UImage (same _ _ hU iU)
  have realized := context'.realize_l hZF nv θ χ' ready.source (moved.mp old) movedχ eqn eqκ eqU oldEq
    ((eqχ 3).trans τχ) ((eqχ 1).trans mχ) ((eqχ 0).trans uχ)
    (Eq.mp (congrArg (fun a => M.mem a ω) mχ) hmω) program' relativeSubtype
  obtain ⟨P, ν, pool, below, witness⟩ := realized
  -- 同一候选的低层实现、最大序数查询及原节点在目标层合流，保留原排列。
  have eqe := hj.1.1.1.2 (ρ₀.bound 17).val (θ.bound 17).val (ρ₀.bound 17).val (images 17) (natural _ heω)
  have candidateDomain := (Formula.satisfies_conj_iff ..).mp candidate |>.1
  simp only [Formula.satisfies_rename, ee_language0_m, ee_domain_pack_m,
    Formula.satisfies_bind, ee_domain_pack0_m, Formula.satisfies_conj_iff] at candidateDomain
  have hωU : M.mem ω (χ.bound 6).val := ωχ ▸ (show M.mem (χ.bound 2).val (χ.bound 6).val from candidateDomain.1.1)
  have witness' : Tg_realized_in_d ω (θ.bound 18).val (θ.bound 24).val (θ.bound 29).val
      (ψ'.bound 3).val (χ'.bound 6).val P (p 13) ν C' := by
    apply Eq.mpr (congrArg (fun n : M.Domain => Tg_realized_in_d ω (θ.bound 18).val n (θ.bound 29).val
      (ψ'.bound 3).val (χ'.bound 6).val P (p 13) ν C') eqn)
    exact Eq.mpr (congrArg (fun m : M.Domain => Tg_realized_in_d ω (θ.bound 18).val (p 3) (θ.bound 29).val m
      (χ'.bound 6).val P (p 13) ν C') ((eqψ 3).trans nψ)) witness
  obtain ⟨εr, eqr, recovered⟩ := tg_recover_read_l (ZF.modelsKP hZF) nv θ ψ' ready.source.omega
    (context'.read_l hZF ready.source).1
    (context'.kernel_mem_l ready.source.transitive ready.source.code (context'.read_l hZF ready.source).1.transitive nv)
    (moved.mp old) movedψ
    ((eqψ 0).trans ωψ) ((eqψ 1).trans (eψ.trans eqe.symm)) ((eqψ 2).trans (lψ.trans eqn.symm))
    (Eq.mpr (congrArg (fun a => M.mem ω a) (eqχ 6)) hωU)
    ⟨Eq.mpr (congr (congrArg M.mem (eqψ 4)) (eqχ 6)) scope.1,
      Eq.mpr (congr (congrArg M.mem (eqψ 5)) (eqχ 6)) scope.2.1,
      Eq.mpr (congr (congrArg M.mem (eqψ 6)) (eqχ 6)) scope.2.2⟩
    (Eq.mpr (congrArg (fun a => M.mem a (p 13)) (eqψ 11)) node)
    (Eq.mpr (congrArg (fun a => M.mem a (p 13)) (eqψ 8)) maximum) witness'
  have imageω := hj.omega_l I hZF source.source.omega source.source.transitive ready.source.transitive my mn source.source.omega_mem
  have ωθ := hj.1.1.1.2 ω (θ.bound 16).val ω (ω₀ ▸ images 16) imageω
  have hlχ := (eqχ 4).trans (ℓχ.symm.trans (lψ.trans eqn.symm))
  have hnχ := ((eqψ 3).trans nψ).trans ((eqχ 1).trans mχ).symm
  have sameRecovery : ∀ i : Fin 10, εr.bound ([7, 8, 10, 11, 12, 13, 23, 24, 25, 28].get i) =
      [θ.bound 16, θ.bound 17, θ.bound 23, θ.bound 24, χ'.bound 1, χ'.bound 6,
        θ.bound 18, θ.bound 19, θ.bound 20, χ'.bound 0].get i := by
    intro i
    apply Subtype.ext
    exact Fin.cases ((eqr 0).trans ωθ.symm) (Fin.cases (eqr 1) (Fin.cases (eqr 3)
      (Fin.cases (eqr 4) (Fin.cases ((eqr 5).trans hnχ) (Fin.cases (eqr 6)
        (Fin.cases (eqr 16) (Fin.cases (eqr 17) (Fin.cases (eqr 18)
          (Fin.cases ((eqr 21).trans ((eqχ 0).trans uχ).symm) (fun j => Fin.elim0 j)))))))))) i
  have belowχ : M.mem (χ'.bound 3).val (θ.bound 15).val :=
    Eq.mpr (congr (congrArg M.mem ((eqχ 3).trans τχ)) eqκ) (bound _ hτL)
  have programθ : Ts_program_in_d ω (θ.bound 24).val (p 14) (p 16) σ C' :=
    Eq.mpr (congrArg (fun n : M.Domain => Ts_program_in_d ω n (p 14) (p 16) σ C') eqn) program'
  -- 恢复节点的标签就是当前真实请求的标签；定义域由同一图唯一确定。
  have ft := (context'.read_l hZF ready.source).1
  have issued₀ := (tg_issued_sat_l (rt_pair_l fs.transitive nc hZF.1 fs.pair)
    (rt_model_ext_l hZF.1 fs.transitive nc) ι).mp issued
  let ζ : Env (rt_model_l C nc) 3 := ⟨fun i => [ι.bound 26, ι.bound 0, ι.bound 23].get i, ι.free⟩
  have ew : (ι.bound 0).val = ω := links 0
  have labels₀ : Fn0_d (ι.bound 26).val ω (ι.bound 23).val := ew ▸
    (fn0_sat_l hZF.1 _ (.bound 0) (.bound 1) (.bound 2)).mp
      ((rt_model_delta_l fs.transitive nc (fn0_delta_l (.bound 0) (.bound 1) (.bound 2)) ζ).mp
        ((fn0_sat_l (rt_model_ext_l hZF.1 fs.transitive nc) ζ (.bound 0) (.bound 1) (.bound 2)).mpr issued₀.labels))
  have label_eq : (εr.bound 16).val = (ι.bound 23).val := (eqr 9).trans ((eqψ 6).trans (queryRequest 5))
  have labels₁ : Fn0_d (ι.bound 26).val ω (εr.bound 16).val := label_eq.symm ▸ labels₀
  obtain ⟨_, labels⟩ := tg_restart_labels_l (ZF.modelsKP hZF) ft.transitive nv εr recovered
    (show Fn0_d (ι.bound 26).val (εr.bound 7).val (εr.bound 16).val from (eqr 0).symm ▸ labels₁)
  let s : Fin 7 → M.Domain := σ
  let pp : Fin 11 → M.Domain := fun i => [ω,(θ.bound 24).val,p 14,p 16,
    s 0,s 1,s 2,s 3,s 4,s 5,s 6].get i
  let μ : Env (rt_model_l C' nv) 11 :=
    ⟨fun i => ⟨pp i, programθ.1 i⟩, fun _ => ⟨ω, (context'.omega_l ready.source.code)⟩⟩
  have numeric := (sc_relative_sat_l ft.transitive nv ts_numeric0_m ts_numeric0_closed_l
    μ ((⟨pp, fun _ => ω⟩ : Env M 11).push C') .newest (fun i => .bound i.succ) rfl (fun _ => rfl)).mp programθ.2
  obtain ⟨πp, eqp₀, v₂, seed₂, a₂, round₂⟩ := tg_restart_read_l
    (context'.kernel_mem_l ready.source.transitive ready.source.code ft.transitive nv) θ χ' εr μ
    (moved.mp old) movedχ recovered numeric labels sameRecovery
    (Subtype.ext (((eqχ 2).trans ωχ).trans ωθ.symm)) (Subtype.ext hlχ)
    (Subtype.ext ωθ.symm) rfl belowχ
  have eqp i := congrArg Subtype.val (eqp₀ i)
  let ρ₂ := tg_round_env_d (tg_restart_env_d θ χ' εr πp v₂) a₂
  -- 恢复图的包含与真实有限函数域，给出沿同一奇数边恰好增加一个点。
  have os := (Formula.satisfies_conj_iff ..).mp (moved.mp old) |>.1
  simp only [tg_seed0_m, Formula.satisfies_rename, tg_seed_m, Formula.satisfies_conj_iff] at os
  obtain ⟨_, _, _, _, _, _, _, oldSucc, _, _, _, _, _, _, _, _, _, _, _, oldNode, _⟩ := os
  have oldNode := (tg_node_source_l ft.transitive nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) _ _ _ _ _ _).mp oldNode
  have oldGraph := oldNode.2.2.1
  have nr := recovered
  simp only [tc_recovered0_m, tc_recovered_m, Formula.satisfies_conj_iff] at nr
  obtain ⟨_, _, _, _, _, _, _, _, _, newNode, _, keep⟩ := nr
  have newNode := (tg_node_source_l ft.transitive nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) _ _ _ _ _ _).mp newNode
  have newGraph := newNode.2.2.1
  have hs := (rt_successor_l ft.transitive nv hZF.1 (θ.bound 23) (θ.bound 22)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp oldSucc)
  have en : (εr.bound 10).val = (θ.bound 23).val := eqr 3
  have newGraph : Tg_graph_d I (θ.bound 23).val (εr.bound 2).val := en ▸ newGraph
  have sub : M.MemberSubset (θ.bound 42).val (εr.bound 2).val := by
    intro r hr
    have hr' : M.mem r (εr.bound 26).val := (eqr 19).symm ▸ hr
    let x : (rt_model_l C' nv).Domain := ⟨r, ft.transitive _ (εr.bound 26).property r hr'⟩
    exact (Formula.satisfies_iff_iff ..).mp ((Formula.satisfies_forall_iff ..).mp keep x) |>.mpr
      ((Formula.satisfies_disj_iff ..).mpr (Or.inl hr'))
  obtain ⟨z, hz, push⟩ := tg_graph_extend_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hs oldGraph newGraph sub
  have digits : (ρ₂.bound 40).val = (ψ.bound 5).val := (eqr 8).trans (eqψ 5)
  have oldDigits := hj.1.1.1.2 _ _ _ (images 40) (fixedZ _ lowS)
  have gs : Tg_graph_d I (θ.bound 22).val (ρ₀.bound 40).val := oldDigits ▸ oldNode.1
  have gt : Tg_graph_d I (θ.bound 23).val (ρ₂.bound 40).val := en ▸ newNode.1
  have played' : Tg_play_d I X R C (ι.bound 4).val (ι.bound 3).val (ι.bound 20).val (ρ₂.bound 40).val := by
    rw [digits]; exact played
  have digitSub := oldPlayed.subset_l I hZF.1 mx owner.source.transitive context.member fs.transitive nc (rt_pair_l fs.transitive nc hZF.1 fs.pair) ι issued
    played' gs gt (fun x hx => (hs x).mpr (Or.inl hx))
  have odd : Tg_odd_d ω H₀ ξ α k G' (ι.bound 1).val (ι.bound 23).val (ι.bound 22).val (ι.bound 7).val
      (ρ₂.bound 19).val (ρ₂.bound 22).val (ρ₂.bound 40).val (ρ₂.bound 42).val :=
    Or.inr ⟨fun eq => ne (Subtype.ext eq), Y, S, μᵣ, Kₕ, η₀, C₀, Lᵣ, Vᵣ, qᵣ,
      (ρ₀.bound 19).val, (ρ₀.bound 22).val, (ρ₀.bound 40).val, (ρ₀.bound 41).val, (ρ₀.bound 42).val, j, (θ.bound 42).val, (θ.bound 22).val, z,
      row, ⟨_, code, rfl, rfl, rfl, rfl, rfl⟩, edge, images 19, images 22, images 42, hs, hz, push,
      fixedZ _ lowS, digitSub, fixedZ _ lowT, labelSub⟩
  have nextSeed := seed₂
  simp only [tg_seed0_m, tg_seed_m, Formula.satisfies_conj_iff] at nextSeed
  have first := (rt_successor_l (context'.read_l hZF ready.source).1.transitive nv hZF.1
    (ρ₂.bound 23) (ρ₂.bound 22)).mp ((Formula.satisfies_isSuccessor_iff ..).mp nextSeed.2.2.2.2.2.2.2.1)
  have state := (tg_issued_sat_l (rt_pair_l fs.transitive nc hZF.1 fs.pair)
    (rt_model_ext_l hZF.1 fs.transitive nc) ι).mp issued
  have first' := (rt_successor_l fs.transitive nc hZF.1 (ι.bound 27) (ι.bound 26)).mp state.first
  have el : (ρ₂.bound 23).val = (ι.bound 27).val := eqn.trans (links 2).symm
  have ek := first.predecessor_eq hZF.1
    ((ready.source.omega.members_areOrdinals (ZF.modelsKP hZF) _ (eqn.symm ▸ (hw ▸ prog.1))).mem first.predecessor_mem)
    (el.symm ▸ first')
  have request : Tg_request_d Eq (fun i => (ι.bound i).val) (fun i => (ρ₂.bound i).val) := by
    intro i
    exact Fin.cases (ωθ.trans (links 0).symm) (Fin.cases (eqe.trans (links 1).symm)
      (Fin.cases ek (Fin.cases el (Fin.cases ((eqχ 1).trans (candidateRequest 1))
        (Fin.cases ((eqp 2).trans (codes 0)) (Fin.cases ((eqp 3).trans (codes 1))
          (Fin.cases ((eqp 4).trans (codes 2)) (Fin.cases ((eqp 5).trans (codes 3))
            (Fin.cases ((eqp 6).trans (codes 4)) (Fin.cases ((eqp 7).trans (codes 5))
              (Fin.cases ((eqp 8).trans (codes 6)) (Fin.cases ((eqp 9).trans (codes 7))
                (Fin.cases ((eqp 10).trans (codes 8)) (Fin.cases ((eqχ 3).trans (candidateRequest 3))
                  (Fin.cases ((eqχ 6).trans (candidateRequest 6)) (Fin.cases ((eqχ 7).trans (candidateRequest 7))
                    (Fin.cases ((eqχ 0).trans (candidateRequest 0))
                      (Fin.cases ((eqr 9).trans ((eqψ 6).trans (queryRequest 5)))
                        (fun j => Fin.elim0 j))))))))))))))))))) i
  -- 偶数操作的末项界正是新轮下界；奇数操作的施加源仍为原偶数模型 X。
  have above₂ : ∀ i μ, Rd_entry_d i μ H' → M.mem μ (ρ₂.bound 39).val ∨ μ = (ρ₂.bound 39).val := by
    change ∀ i μ, Rd_entry_d i μ H' → M.mem μ (θ.bound 15).val ∨ μ = (θ.bound 15).val
    rw [eqκ]
    exact heights
  have hδ₂ := (context'.round_regular_l hZF nv ρ₂ ready ωθ round₂).1
  have oldData := (Formula.satisfies_conj_iff ..).mp (moved.mp old) |>.2
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff] at oldData
  have hLδ₂ : M.mem L.val (ρ₂.bound 18).val := ordinal_down_l (ZF.modelsKP hZF) hLimit.1 hδ₂.1
    (fun x hx => Eq.mpr (congrArg (fun z => M.mem x z) eqκ) (bound x hx)) oldData.2.2.1
  have hκW₂ : M.mem (ρ₂.bound 21).val W := Eq.mpr (congrArg (fun z => M.mem z W) ((eqχ 3).trans τχ))
    (common.ordinal_subset_l hZF owner.source.transitive hW (p 8) hτL)
  have hWCX := ((context.rank_l (ZF.modelsKP hZF) owner.source.transitive owner.source.code).rank_l hZF owner.source.transitive context.member (context.limit_l (ZF.modelsKP hZF) owner.source.transitive owner.source.code) L.property hW common).1
  have evenNode := ext.2.2.1 ξ c hc
  obtain ⟨β₂, T₂, J₂, G₂, E₂, H₂, c₂, j₂, N₂, R₂, K₂, L₂, F₂, κ₂, U₂, D₂, u₂, η₂, C₂, W₂,
    next₂, ext₂, target₂, edge₂, mn₂, ready₂, ultra₂, critical₂, payload₂, limit₂, bound₂, subset₂, heights₂,
    iU₂, iD₂, iu₂, reply₂, iη₂, iC₂, context₂, legal₂, hW₂, hWC₂, common₂, level₂, hQ₂, hw₂, agreement₂, fixed₂⟩ :=
    context'.round_l hZFC nv ρ₂ context ready owner next ext.1 target evenNode mn mx
      level.member level.hierarchy hW common hLimit hWCX hLδ₂ hκW₂ ωθ above₂ round₂
  -- 根图按实际树的复合律延伸；旧字母表仍严格低于新临界点。
  obtain ⟨π₂, root₂⟩ := next₂.tree.diagram.map_l hZF
    (next₂.tree.diagram.order.root_l hZF ho β ext₂.1.predecessor_mem)
  have oldEvenRoot := (ext.2.2.2.1 o ξ π succ.predecessor_mem).mpr root
  have oldRoot₂ := (ext₂.2.2.2.1 o ξ π ((next.tree.diagram.model_domain ξ).mpr ⟨c, evenNode⟩)).mpr oldEvenRoot
  have iRoot₂ := next₂.tree.diagram.comp o ξ β π j₂ π₂ oldRoot₂ edge₂ root₂ Cᵣ C C₂ iRoot iC₂
  obtain ⟨_, _, _, hτ, _, _, _, _, exceeds, _⟩ := facts
  have hτ := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) (ρ.bound 8)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp hτ)
  simp only [tx_exceeds_m, Formula.satisfies_bind, tx_exceeds0_m,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at exceeds
  have lower₂ : M.MemberSubset γ (ρ₂.bound 21).val := by
    exact Eq.mpr (congrArg (fun z => M.MemberSubset γ z) ((eqχ 3).trans τχ))
      (fun x hx => hτ.1.transitive (p 1) exceeds.1 x (lower x hx))
  have roundData := (Formula.satisfies_conj_iff ..).mp round₂ |>.2
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff] at roundData
  have hκL₂ := limit₂.1.transitive (ρ₂.bound 15).val bound₂ (ρ₂.bound 21).val roundData.2.1
  have fixedCopy₂ := fixed₂
  obtain ⟨V₂, hV₂, rank₂, _, _, pointwise₂⟩ := fixedCopy₂
  have hgL₂ := ordinal_down_l (ZF.modelsKP hZF) (nr.ordinal_l nz) limit₂.1 lower₂ hκL₂
  have hgW₂ := common₂.ordinal_subset_l hZF ready.source.transitive hW₂ γ hgL₂
  obtain ⟨hzW₂, rzW₂⟩ := common₂.rank_l hZF ready.source.transitive hW₂ limit₂ hgW₂ nz nr
  have sz₂ := (rank₂.compare_l hZF owner.source.transitive hV₂ az ar lower₂).1
  have anchor₂ := Tg_anchor_d.of_mem_l hZF mn₂ ready₂.source.transitive
    (ready₂.source.transitive W₂ level₂.member γ hgW₂) (ready₂.source.transitive W₂ level₂.member Z₀ hzW₂)
    (level₂.hierarchy.of_rank_l ready₂.source.transitive level₂.member hzW₂ rzW₂)
    (fun x hx => next₂.tree.diagram.comp o ξ β π j₂ π₂ oldRoot₂ edge₂ root₂ x x x
      (af x hx) (pointwise₂ x (sz₂ x hx)))
  have κθ : M.MemberSubset (ρ₂.bound 21).val L.val := by
    change M.MemberSubset (χ'.bound 3).val L.val
    rw [(eqχ 3).trans τχ]
    exact hLimit.1.transitive _ hτL
  have past := context'.past_update_l hZF ready nv ρ₂ round₂ ωθ owner.source.transitive hW common
    level.member level.hierarchy hLimit κθ limit₂ hWC₂ common₂ bound₂ hw₂ (limit₂.1.transitive _ hκL₂)
    ready₂.source.transitive level₂.member level₂.hierarchy subset₂ hV₂ rank₂ pointwise₂
    (fun i d hi => ext₂.2.2.1 i d (ext.2.2.1 i d hi)) (ext₂.2.2.1 α d' target) mn
  have high : M.MemberSubset γ (ρ₂.bound 15).val := fun x hx =>
    (limit₂.1.mem bound₂).transitive _ roundData.2.1 x (lower₂ x hx)
  have eκ : (ρ₂.bound 21).val = (ι.bound 24).val := request 14
  have eU : (ρ₂.bound 31).val = (ι.bound 30).val := request 15
  have eD : (ρ₂.bound 32).val = (ι.bound 31).val := request 16
  have eu : (ρ₂.bound 34).val = (ι.bound 25).val := request 17
  obtain ⟨p₁, entry₁, pay₁⟩ := payload
  have lo := It_lower_d.mem_l I hZF mx owner.source.transitive ag hγ.1
    (owner.source.transitive C context.member (p 1) (ρ.bound 1).property) lower
  have lower₁ := it_payload_bound_l I (ZF.modelsKP hZF) next.tree.move_function entry₁ pay₁
    (ext.2.2.1 ξ c hc) mx.1 lo
  exact ⟨k, β, T', J', G', E', H', d', N, R', L.val, K₀, η', C', π',
    next, ext, target, mn, ready, context', root', iRoot', anchor', lower₁, nv, ρ₂, round₂, request, high, odd,
    ⟨by change M.mem (ρ₂.bound 40).val Z₀; rw [digits]; exact queryLow 5,
      by change Tg_play_d I X R C (ι.bound 4).val (ι.bound 3).val (ι.bound 20).val (ρ₂.bound 40).val; rw [digits]; exact played⟩,
    β₂, T₂, J₂, G₂, E₂, H₂, c₂, j₂, N₂, R₂, K₂, L₂, F₂, κ₂, U₂, D₂, u₂, η₂, C₂, W₂,
    π₂, next₂, ext₂, target₂, edge₂, mn₂, ready₂, eκ ▸ ultra₂, eκ ▸ critical₂, eκ ▸ payload₂, limit₂, bound₂, subset₂, heights₂,
    eU ▸ iU₂, eD ▸ iD₂, eu ▸ iu₂, reply₂, iη₂, iC₂, context₂, hW₂, common₂, level₂,
    root₂, iRoot₂, anchor₂, eκ ▸ past⟩

end YesMetaZFC.SetTheory.LargeCardinal
