import YesMetaZFC.SetTheory.LargeCardinal.ExtenderReadSource
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingRelative

/-! # 原关系后继的有限读写闭性

有限空间用一个固定句子整体传递，量化下一层的全部新参数。解码时先取得
配对、并集和真实 ω，再以背景内部自然数归纳回收全部有限图。因此函数空间
包括背景内部非标准有限长度；不要求高模型传递或对外部 ω 列封闭。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def fs_read0_m {d} (ω : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isOmega⌝ₚ(⌜ω⌝ₛ) ∧ ⌜Formula.isLimitOrdinal⌝ₚ(⌜ω⌝ₛ) ∧
  (∀ a b, ∃ p, ⌜pair0_m⌝ₚ(p, a, b)) ∧
  (∀ a, ∃ p, ⌜Formula.isUnion⌝ₚ(p, a)) ∧
  (∀ A, ∀ n ∈ ⌜ω⌝ₛ, ∃ D, ∀ f, f ∈ D ↔ ⌜fn0_m⌝ₚ(n, A, f))⟫
derive_free_closed fs_read0_m

theorem fs_read0_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω : Term d) :
    Formula.satisfies ρ (fs_read0_m ω) ↔
      M.IsOmega (ω.eval ρ) ∧ M.IsLimitOrdinal (ω.eval ρ) ∧
      (∀ a b, ∃ p, Pair_d M p a b) ∧
      (∀ a, ∃ p, M.IsUnionOf p a) ∧
      ∀ A n, M.mem n (ω.eval ρ) → ∃ D, Ep_space_d A n D := by
  simp only [fs_read0_m, Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff,
    Formula.satisfies_isLimitOrdinal_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_forallMem_iff, pair0_sat_l hE,
    Formula.satisfies_isUnion_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    fn0_sat_l hE, Definitional.Term.eval_weaken, Ep_space_d]; rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

/-- 两个有限闭包方向都涉及全部背景内部自然数，而非外部逐个标准长度。 -/
theorem fs_read0_relative_l {Γ : M.Domain} (trans : M.TransitiveSet Γ)
    (nc : Nonempty {x // M.mem x Γ}) (w : (rt_model_l Γ nc).Domain) :
    Formula.satisfies (⟨fun _ => w, fun _ => w⟩ : Env (rt_model_l Γ nc) 1) (fs_read0_m .newest) ↔
      M.IsOmega w.val ∧ Fs_read_d w.val Γ ∧
        ∀ a, M.mem a Γ → ∃ p, M.mem p Γ ∧ M.IsUnionOf p a := by
  have ext := rt_model_ext_l hZF.1 trans nc
  have pair (p a b : (rt_model_l Γ nc).Domain) :
      Pair_d (rt_model_l Γ nc) p a b ↔ Pair_d M p.val a.val b.val := by
    let ρ : Env (rt_model_l Γ nc) 3 := ⟨Fin.cases p (Fin.cases a (fun _ => b)), fun _ => w⟩
    have read := (pair0_sat_l ext ρ .newest (.bound 1) (.bound 2)).symm.trans
      ((rt_model_delta_l trans nc (pair0_delta_l ..) ρ).trans (pair0_sat_l hZF.1 ..))
    exact read
  rw [fs_read0_sat_l ext]
  constructor
  · rintro ⟨localω, limit, pairs, unions, spaces⟩
    have limit := (rt_limit_l trans nc (ZF.modelsKP hZF) w).mp limit
    -- 相对自然数集既是实际极限序数，又在本层中最小，故正是背景 ω。
    obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
    have real : M.IsOmega w.val := by
      rcases (hω.isOrdinal hZF).trichotomy hZF.1 limit.1 (KP.difference_exists_d (ZF.modelsKP hZF))
        (KP.intersection_exists_d (ZF.modelsKP hZF) ω w.val) with eq | lt | gt
      · exact hZF.1.eq_of_same_members ω w.val eq ▸ hω
      · let v : (rt_model_l Γ nc).Domain := ⟨ω, trans w.val w.property ω lt⟩
        have hv := rt_omega_l trans nc hZF.1 v hω
        have eq := ext.eq_of_same_members v w (fun x => ⟨hv.2 w localω.1 x, localω.2 v hv.1 x⟩)
        exact congrArg Subtype.val eq ▸ hω
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) w.val
          (hω.subset_limitOrdinal hZF limit w.val gt)).elim
    have hp a b (ha : M.mem a Γ) (hb : M.mem b Γ) : ∃ p, M.mem p Γ ∧ Pair_d M p a b := by
      obtain ⟨p, code⟩ := pairs ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨p.val, p.property, (pair p ⟨a, ha⟩ ⟨b, hb⟩).mp code⟩
    have hu a (ha : M.mem a Γ) : ∃ p, M.mem p Γ ∧ M.IsUnionOf p a := by
      obtain ⟨p, code⟩ := unions ⟨a, ha⟩
      exact ⟨p.val, p.property, (rt_union_l trans nc p ⟨a, ha⟩).mp code⟩
    have finite {n A f} := sc_finite_function_l hZF (A := A) (n := n) (f := f)
      real trans hp hu w.property
    refine ⟨real, ⟨trans, w.property, hp, fun _ _ _ hn hA hf => finite hA hn hf, ?_⟩, hu⟩
    intro A n hA hn
    let a : (rt_model_l Γ nc).Domain := ⟨A, hA⟩
    let m : (rt_model_l Γ nc).Domain := ⟨n, trans w.val w.property n hn⟩
    obtain ⟨D, code⟩ := spaces a m hn
    refine ⟨D.val, D.property, fun f => ⟨fun hf => ?_, fun hf => ?_⟩⟩
    · exact (rt_fn_l trans nc hZF.1 m a ⟨f, trans D.val D.property f hf⟩).mp
        ((code ⟨f, trans D.val D.property f hf⟩).mp hf)
    · let g : (rt_model_l Γ nc).Domain := ⟨f, finite (trans A hA) hn hf⟩
      exact (code g).mpr ((rt_fn_l trans nc hZF.1 m a g).mpr hf)
  · rintro ⟨hω, fs, unions⟩
    refine ⟨rt_omega_l trans nc hZF.1 w hω,
      (rt_limit_l trans nc (ZF.modelsKP hZF) w).mpr (hω.isLimitOrdinal hZF), ?_, ?_, ?_⟩
    · intro a b
      obtain ⟨p, hp, code⟩ := fs.pair a.val b.val a.property b.property
      exact ⟨⟨p, hp⟩, (pair ⟨p, hp⟩ a b).mpr code⟩
    · intro a
      obtain ⟨p, hp, code⟩ := unions a.val a.property
      exact ⟨⟨p, hp⟩, (rt_union_l trans nc ⟨p, hp⟩ a).mpr code⟩
    · intro a n hn
      obtain ⟨D, hD, code⟩ := fs.spaces a.val n.val a.property hn
      exact ⟨⟨D, hD⟩, fun f => (code f.val).trans (rt_fn_l trans nc hZF.1 n a f).symm⟩

/-- 原关系边传递固定有限闭包句子；新层及其 ω 来自同一完整实现图。 -/
theorem Fs_read_d.map_layer_l {ω c Y S c' Z T j B Γ H H' k k' : M.Domain}
    (source : Fs_read_d ω B) (hω : M.IsOmega ω)
    (unions : ∀ a, M.mem a B → ∃ p, M.mem p B ∧ M.IsUnionOf p a)
    (model : Smdl_d I c Y S) (next : Smdl_d I c' Z T) (embed : Smap_d I ω c c' Y Z j)
    (left : Rr_layer_d I B Y S H k) (right : Rr_layer_d I Γ Z T H' k')
    (hHH : Rd_entry_d H H' j) :
    Fs_read_d ω Γ ∧ (∀ a, M.mem a Γ → ∃ p, M.mem p Γ ∧ M.IsUnionOf p a) ∧
      ∃ x y, Rd_entry_d ω x k ∧ Rd_entry_d x y j ∧ Rd_entry_d ω y k' := by
  obtain ⟨x, hx, hwx⟩ := left.injection.1.2.2 ω source.omega_mem
  obtain ⟨y, _, hxy⟩ := embed.1.1.2.2 x hx
  obtain ⟨w, hw, _⟩ := (right.image y).mp
    ((embed.relation_l I hZF hω model next hxy hHH).mp ((left.image x).mpr ⟨ω, source.omega_mem, hwx⟩))
  let nb : Nonempty {x // M.mem x B} := ⟨⟨ω, source.omega_mem⟩⟩
  let ng : Nonempty {x // M.mem x Γ} := ⟨⟨w, hw⟩⟩
  let ρ : Env (rt_model_l B nb) 1 := ⟨fun _ => ⟨ω, source.omega_mem⟩, fun _ => ⟨ω, source.omega_mem⟩⟩
  have valid := (fs_read0_relative_l hZF source.transitive nb ⟨ω, source.omega_mem⟩).mpr ⟨hω, source, unions⟩
  obtain ⟨η, values, truth⟩ := embed.relative_image_l hZF hω model next left right nb ng hHH
    (fs_read0_m .newest) (by simp -implicitDefEqProofs) ρ
  have same := Formula.closed_env_l (fs_read0_m .newest) (by simp -implicitDefEqProofs)
    (show (⟨fun _ => η.bound 0, fun _ => η.bound 0⟩ : Env (rt_model_l Γ ng) 1).bound = η.bound from
      funext fun i => congrArg η.bound (Subsingleton.elim 0 i))
  obtain ⟨real, fs, union⟩ := (fs_read0_relative_l hZF right.transitive ng (η.bound 0)).mp
    (same.mpr (truth.mp valid))
  have eq : (η.bound 0).val = ω :=
    hZF.1.eq_of_same_members _ _ (fun z => ⟨real.2 ω hω.1 z, hω.2 _ real.1 z⟩)
  exact ⟨eq ▸ fs, union, by simpa only [eq] using values 0⟩

end YesMetaZFC.SetTheory.LargeCardinal
