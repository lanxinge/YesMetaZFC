import YesMetaZFC.Model.SetTheory.Types.Embedding
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Step
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawOwnedCopy
import YesMetaZFC.Model.SetTheory.Internal.FiniteSpaceBounded
import YesMetaZFC.SetTheory.LargeCardinal.Extender.OmegaClosed
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawRankSource
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial
import YesMetaZFC.Model.SetTheory.Types.KappaCode
import YesMetaZFC.Model.SetTheory.Internal.TupleCode

/-! # 弹性查询的合法名字列

原 n 个变量后依次放置 ω、n、指定常量 δ、κ。非零极限 κ 已包含全部
内部自然数；ω<κ 时 ω∈Vκ，ω=κ 时使用已有的 κ 常量。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Ee_stretch_code_d (ω n κ v d e z p : M.Domain) : Prop := ∃ C kw kn kk,
  KPair_d M p z C ∧ KPair_d M kw ω ω ∧ KPair_d M kn n n ∧ KPair_d M kk κ κ ∧
    (∀ i, M.mem i n → Rd_entry_d i i C) ∧ Rd_entry_d n kw C ∧ Rd_entry_d v kn C ∧
      Rd_entry_d d n C ∧ Rd_entry_d e kk C

theorem ee_column_l {ω n v d e κ U N : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω)
    (hv : M.SuccessorOf v n) (hd : M.SuccessorOf d v) (he : M.SuccessorOf e d)
    (hωU : M.mem ω U) (hnU : M.mem n U) (hκU : M.mem κ U) (names : Tn_names_d n U N) :
    ∃ b C kw kn kk, M.SuccessorOf b e ∧ M.mem b ω ∧ M.IsSetFunctionFromTo I C b N ∧
      (I).Codes kw ω ω ∧ (I).Codes kn n n ∧ (I).Codes kk κ κ ∧
      (∀ i, M.mem i n → Rd_entry_d i i C) ∧
      Rd_entry_d n kw C ∧ Rd_entry_d v kn C ∧ Rd_entry_d d n C ∧ Rd_entry_d e kk C := by
  have ho := hω.members_areOrdinals (ZF.modelsKP hZF) n hn
  have vo := KP.successor_isOrdinal (ZF.modelsKP hZF) ho hv
  have dord := KP.successor_isOrdinal (ZF.modelsKP hZF) vo hd
  have eo := KP.successor_isOrdinal (ZF.modelsKP hZF) dord he
  have vω : M.mem v ω := by obtain ⟨v', h, hω⟩ := hω.1.2 n hn; exact Structure.SuccessorOf.eq hZF.1 h hv ▸ hω
  have dω : M.mem d ω := by obtain ⟨d', h, hω⟩ := hω.1.2 v vω; exact Structure.SuccessorOf.eq hZF.1 h hd ▸ hω
  have eω : M.mem e ω := by obtain ⟨e', h, hω⟩ := hω.1.2 d dω; exact Structure.SuccessorOf.eq hZF.1 h he ▸ hω
  obtain ⟨b, hb, hbω⟩ := hω.1.2 e eω
  obtain ⟨kw, hw⟩ := (I).total ω ω
  obtain ⟨kn, hnn⟩ := (I).total n n
  obtain ⟨kk, hk⟩ := (I).total κ κ
  let φ : BinarySchema 0 := { body := Formula.extensionalEq .newest (.bound 1) }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => n⟩
  have sat i x : φ.denote ρ i x ↔ x = i := Formula.satisfies_extensionalEq_iff_eq hZF.1 ..
  obtain ⟨f, base, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := n) (target := N)
    (fun i _ => ⟨i, (sat i i).mpr rfl⟩)
    (fun i _ x y hx hy => ((sat i x).mp hx).trans ((sat i y).mp hy).symm)
    (fun i x hi hx => ((sat i x).mp hx).symm ▸ (names i).mpr (Or.inl hi))
  obtain ⟨f₁, h₁, old₁, end₁⟩ := tt_column_append_l hZF ho hv base ((names kw).mpr (Or.inr (Or.inr ⟨ω, hωU, hw⟩)))
  obtain ⟨f₂, h₂, old₂, end₂⟩ := tt_column_append_l hZF vo hd h₁ ((names kn).mpr (Or.inr (Or.inr ⟨n, hnU, hnn⟩)))
  obtain ⟨f₃, h₃, old₃, end₃⟩ := tt_column_append_l hZF dord he h₂ ((names n).mpr (Or.inr (Or.inl rfl)))
  obtain ⟨C, hC, old₄, end₄⟩ := tt_column_append_l hZF eo hb h₃ ((names kk).mpr (Or.inr (Or.inr ⟨κ, hκU, hk⟩)))
  have ne := (he n).mpr (Or.inl ((hd n).mpr (Or.inl hv.predecessor_mem)))
  have ve := (he v).mpr (Or.inl hd.predecessor_mem)
  refine ⟨b, C, kw, kn, kk, hb, hbω, hC, hw, hnn, hk, ?_, ?_, ?_, ?_, end₄⟩
  · intro i hi
    exact (old₄ i i (eo.transitive n ne i hi)).mpr ((old₃ i i ((hd i).mpr (Or.inl ((hv i).mpr (Or.inl hi))))).mpr
      ((old₂ i i ((hv i).mpr (Or.inl hi))).mpr ((old₁ i i hi).mpr ((graph i i).mpr ⟨hi, (sat i i).mpr rfl⟩))))
  · exact (old₄ n kw ne).mpr ((old₃ n kw ((hd n).mpr (Or.inl hv.predecessor_mem))).mpr ((old₂ n kw hv.predecessor_mem).mpr end₁))
  · exact (old₄ v kn ve).mpr ((old₃ v kn hd.predecessor_mem).mpr end₂)
  · exact (old₄ d n he.predecessor_mem).mpr end₃

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 指定扩展器的实际类型伸展

先取同一实际超幂中的集合像，再按目标查询域投影。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Et_stretch_d (hZF : M.Models ZF) (ω κ L F X R t D v : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ b d N S i t', Smem_d I b X R ∧ Smem_d I d N S ∧ It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F b d i ∧
    Rd_entry_d t t' i ∧ ∀ p, M.mem p v ↔ M.mem p D ∧ M.mem p t'

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 类型伸展的有界矩阵

在低秩传递容器中塌缩全部有界代表，以常值节点读取原类型的像，再按查询域
取交。节点、求值图和像类型都限定在原所属源内，整个矩阵为 Δ₀。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Eb_stretch_d (ω κ L K X B F t D v : M.Domain) : Prop :=
  ∃ A, M.mem A X ∧ ∃ Q, M.mem Q X ∧ ∃ Y, M.mem Y X ∧ ∃ e, M.mem e X ∧ ∃ y, M.mem y X ∧
    Eb_collapse_d ω κ L K X B F A Q Y e ∧ Eb_const_d X B A e t y ∧
      ∀ p, M.mem p v ↔ M.mem p D ∧ M.mem p y

def et_stretch0_m {d} (ω κ L K X B F H t D v : Term d) : Formula 1 d := set[d] ⟪
  ∃ A ∈ ⌜X⌝ₛ, ∃ Q ∈ ⌜X⌝ₛ, ∃ Y ∈ ⌜X⌝ₛ, ∃ e ∈ ⌜X⌝ₛ, ∃ y ∈ ⌜X⌝ₛ,
    ⌜eb_collapse_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜K⌝ₛ, ⌜X⌝ₛ, ⌜B⌝ₛ, ⌜F⌝ₛ, A, Q, Y, e, ⌜H⌝ₛ) ∧
    ⌜eb_const_m⌝ₚ(⌜X⌝ₛ, ⌜B⌝ₛ, A, e, ⌜t⌝ₛ, y) ∧
    ⌜v⌝ₛ ⊆ ⌜D⌝ₛ ∧ (∀ p ∈ ⌜D⌝ₛ, p ∈ ⌜v⌝ₛ ↔ p ∈ y)⟫
derive_free_closed et_stretch0_m

theorem et_stretch0_delta_l {d} (ω κ L K X B F H t D v : Term d) :
    (et_stretch0_m ω κ L K X B F H t D v).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (eb_collapse_delta_l ..) (.conj (eb_const_delta_l ..)
      (.conj (.atom ..) (.forallMem _ (.iff (.mem ..) (.mem ..))))))))))

theorem et_stretch0_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω κ L K X B F H t D v : Term d)
    (seq : Fseq_space_d (kp_pair_l hKP) (ω.eval ρ) (L.eval ρ) (H.eval ρ)) :
    Formula.satisfies ρ (et_stretch0_m ω κ L K X B F H t D v) ↔
      Eb_stretch_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (K.eval ρ) (X.eval ρ) (B.eval ρ)
        (F.eval ρ) (t.eval ρ) (D.eval ρ) (v.eval ρ) := by
  let w (a : Term d) := a.weaken.weaken.weaken.weaken.weaken
  have collapse (A Q Y e y : M.Domain) :
      Formula.satisfies (((((ρ.push A).push Q).push Y).push e).push y)
        (eb_collapse_m (w ω) (w κ) (w L) (w K) (w X) (w B) (w F)
          Term.newest.weaken.weaken.weaken.weaken Term.newest.weaken.weaken.weaken
          Term.newest.weaken.weaken Term.newest.weaken (w H)) ↔
      Eb_collapse_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (K.eval ρ) (X.eval ρ) (B.eval ρ) (F.eval ρ) A Q Y e := by
    simpa only [w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using
      eb_collapse_sat_l hKP (((((ρ.push A).push Q).push Y).push e).push y)
        (w ω) (w κ) (w L) (w K) (w X) (w B) (w F)
        Term.newest.weaken.weaken.weaken.weaken Term.newest.weaken.weaken.weaken
        Term.newest.weaken.weaken Term.newest.weaken (w H)
        (by simpa only [w, Definitional.Term.eval_weaken] using seq)
  dsimp only [w] at collapse
  simp only [et_stretch0_m, Eb_stretch_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    collapse, eb_const_sat_l hKP.1, Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
  refine exists_congr fun A => and_congr_right fun _ => exists_congr fun Q => and_congr_right fun _ =>
    exists_congr fun Y => and_congr_right fun _ => exists_congr fun e => and_congr_right fun _ =>
      exists_congr fun y => and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  exact ⟨fun ⟨sub, all⟩ p => ⟨fun hp => ⟨sub p hp, (all p (sub p hp)).mp hp⟩,
    fun ⟨hp, hy⟩ => (all p hp).mpr hy⟩, fun cut =>
      ⟨fun p hp => ((cut p).mp hp).1, fun p hp => (cut p).trans (and_iff_right hp)⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有界矩阵与原实际类型伸展的等价

同一扩展器的原超幂提供实际存在性；小关系的坍塌将全部证据放回所属源。
反向读取使用给定坍塌的唯一性，不把低秩像替换成另一个嵌入的像。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Eb_stretch_d.read_l {ω κ K L X R F c d j N S B t D v : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (hm : Smem_d I c X R) (hn : Smem_d I d N S) (ultra : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c d j)
    (hB : M.mem B X) (trans : M.TransitiveSet B) (ht : M.mem t B)
    (h : Eb_stretch_d ω κ L K X B F t D v) : Et_stretch_d hZF ω κ L F X R t D v := by
  obtain ⟨A, _, Q, _, Y, _, e, _, y, _, collapse, value, cut⟩ := h
  have image := ((collapse.image_l hZF source family hm hn ultra hB trans).2 t y ht).mp value
  exact ⟨c, d, N, S, j, y, hm, hn, ultra, image, cut⟩

theorem Et_stretch_d.bounded_l {ω κ K L X R F V B t D v : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (power : Sc_power_d X) (family : Em_source_d ω κ L X F)
    (hL : M.mem L X) (hF : M.mem F X) (hl : M.IsLimitOrdinal L) (level : Er_level_d X L V)
    (hκ : M.mem κ V) (hB : M.mem B V) (trans : M.TransitiveSet B) (ht : M.mem t B)
    (h : Et_stretch_d hZF ω κ L F X R t D v) : Eb_stretch_d ω κ L K X B F t D v := by
  have hBX := source.transitive V level.member B hB
  obtain ⟨c, d, N, S, j, y, hm, hn, ultra, image, cut⟩ := h
  obtain ⟨B', _, hBB⟩ := (ultra.elementary_l hZF hm.1 hn.1).1.1.2.2 B hBX
  obtain ⟨hB', A, Q, e, collapse⟩ := it_ultra_owned_image_l hZF source power family hm hn ultra
    hL hF hl level hκ hB trans hBB
  have value := ((collapse.image_l hZF source family hm hn ultra hBX trans).2 t y ht).mpr image
  have owned : M.mem A X ∧ M.mem Q X ∧ M.mem e X ∧ M.mem y X := by
    obtain ⟨_, _, _, _, _, pool, _, _, _, hQ, he, _, _, _, _, map, _⟩ := collapse
    obtain ⟨u, _, _, _, _, _, _, _, _, _, _, huy⟩ := value
    exact ⟨pool.carrier, hQ, he, source.transitive B' hB' y (map.function.bound_l huy).2⟩
  exact ⟨A, owned.1, Q, owned.2.1, B', hB', e, owned.2.2.1, y, owned.2.2.2, collapse, value, cut⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 类型伸展的单一原有界公式

有限列空间和传递容器均由公式内部量化。实际源的有限列闭包识别这些空间，
相对极限秩段提供一个低秩容器，完整等价式读取原来的实际类型伸展。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def et_stretch_m {d} (ω κ L X F t D v : Term d) : Formula 1 d := set[d] ⟪
  ∃ K ∈ ⌜X⌝ₛ, ∃ H ∈ ⌜X⌝ₛ, ∃ B ∈ ⌜X⌝ₛ,
    ⌜fs_space0_m⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ, ⌜κ⌝ₛ, K) ∧ ⌜fs_space0_m⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ, ⌜L⌝ₛ, H) ∧
    ⌜Formula.isTransitive⌝ₚ(B) ∧ ⌜t⌝ₛ ∈ B ∧
    ⌜et_stretch0_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, K, ⌜X⌝ₛ, B, ⌜F⌝ₛ, H, ⌜t⌝ₛ, ⌜D⌝ₛ, ⌜v⌝ₛ)⟫
derive_free_closed et_stretch_m

theorem et_stretch_delta_l {d} (ω κ L X F t D v : Term d) : (et_stretch_m ω κ L X F t D v).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.conj (fs_space0_delta_l ..) (.conj (fs_space0_delta_l ..)
    (.conj (Formula.isTransitive_delta0 _) (.conj (.mem ..) (et_stretch0_delta_l ..)))))))

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem et_stretch_sat_l {d K₀ R V c c' N S j} (ρ : Env M d) (ω κ L X F t D v : Term d)
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval ρ) (κ.eval ρ) K₀ (X.eval ρ) R) (power : Sc_power_d (X.eval ρ))
    (family : Em_source_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (X.eval ρ) (F.eval ρ))
    (hm : Smem_d I c (X.eval ρ) R) (hn : Smem_d I c' N S)
    (ultra : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) c c' j)
    (hL : M.mem (L.eval ρ) (X.eval ρ)) (hF : M.mem (F.eval ρ) (X.eval ρ))
    (hl : M.IsLimitOrdinal (L.eval ρ)) (level : Er_level_d (X.eval ρ) (L.eval ρ) V)
    (hκ : M.mem (κ.eval ρ) V) (ht : M.mem (t.eval ρ) V) :
    Formula.satisfies ρ (et_stretch_m ω κ L X F t D v) ↔
      Et_stretch_d hZF (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) (X.eval ρ) R (t.eval ρ) (D.eval ρ) (v.eval ρ) := by
  obtain ⟨H₀, hH₀, seq⟩ := (source.sequences_l (ZF.modelsKP hZF)).1 (L.eval ρ) hL
  let w (a : Term d) := a.weaken.weaken.weaken
  have sk (K H B : M.Domain) : Formula.satisfies (((ρ.push K).push H).push B)
      (fs_space0_m (w ω) (w X) (w κ) Term.newest.weaken.weaken) ↔ K = K₀ := by
    simpa only [w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using
      fs_space0_iff_l (ZF.modelsKP hZF) (K₀ := K₀) (((ρ.push K).push H).push B)
        (w ω) (w X) (w κ) Term.newest.weaken.weaken
        (by simpa only [w, Definitional.Term.eval_weaken] using (source.finite_l (ZF.modelsKP hZF)))
        (by simpa only [w, Definitional.Term.eval_weaken, Structure.MemberSubset] using source.transitive K₀ source.finite.mem_l)
  have sl (K H B : M.Domain) : Formula.satisfies (((ρ.push K).push H).push B)
      (fs_space0_m (w ω) (w X) (w L) Term.newest.weaken) ↔ H = H₀ := by
    simpa only [w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using
      fs_space0_iff_l (ZF.modelsKP hZF) (K₀ := H₀) (((ρ.push K).push H).push B)
        (w ω) (w X) (w L) Term.newest.weaken
        (by simpa only [w, Definitional.Term.eval_weaken] using seq)
        (by simpa only [w, Definitional.Term.eval_weaken, Structure.MemberSubset] using source.transitive H₀ hH₀)
  have core (K B : M.Domain) : Formula.satisfies (((ρ.push K).push H₀).push B)
      (et_stretch0_m (w ω) (w κ) (w L) Term.newest.weaken.weaken (w X) .newest (w F)
        Term.newest.weaken (w t) (w D) (w v)) ↔
      Eb_stretch_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) K (X.eval ρ) B (F.eval ρ) (t.eval ρ) (D.eval ρ) (v.eval ρ) := by
    simpa only [w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using
      et_stretch0_sat_l (ZF.modelsKP hZF) (((ρ.push K).push H₀).push B)
        (w ω) (w κ) (w L) Term.newest.weaken.weaken (w X) .newest (w F)
        Term.newest.weaken (w t) (w D) (w v)
        (by simpa only [w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using seq)
  dsimp only [w] at sk sl core
  simp only [et_stretch_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    sk, sl, Formula.satisfies_isTransitive_iff, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨K, _, H, _, B, hB, eqK, eqH, trans, htB, matrix⟩
    subst K H
    exact ((core K₀ B).mp matrix).read_l hZF source family hm hn ultra hB trans htB
  · intro stretch
    have htX := source.transitive V level.member (t.eval ρ) ht
    obtain ⟨P, hP, pair⟩ := (source.algebra_l (ZF.modelsKP hZF)).pair (t.eval ρ) (t.eval ρ) htX htX
    have hPV := level.hierarchy.pair_mem_l hZF source.transitive level.member hl ht ht hP pair
    obtain ⟨B, hB, trans, sub⟩ := sc_rank_cover_l source.transitive level.member level.hierarchy P hPV
    have htB := sub (t.eval ρ) ((pair (t.eval ρ)).mpr (Or.inl rfl))
    exact ⟨K₀, source.finite.mem_l, H₀, hH₀, B, source.transitive V level.member B hB,
      rfl, rfl, trans, htB, (core K₀ B).mpr (stretch.bounded_l hZF source power family hL hF hl level hκ hB trans htB)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原伸展公式在传递外层中的精确读取

有界矩阵的全部见证留在所属源中，因此外层只需传递并拥有公式参数。
有界可数闭源从原短扩展器判断自动构造良基超幂；外层无需满足 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 同源的有界可数闭性直接给出实际超幂，不向调用者索取超幂或测度族见证。 -/
theorem et_stretch_closed_l {d K R V} (ρ : Env M d) (ω κ L X F t D v : Term d)
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval ρ) (κ.eval ρ) K (X.eval ρ) R)
    (closed : Sc_bounded_omega_closed_d I (ω.eval ρ) (X.eval ρ) R) (power : Sc_power_d (X.eval ρ))
    (loc : It_local_d I (ω.eval ρ) (X.eval ρ) R (κ.eval ρ) (L.eval ρ) (F.eval ρ))
    (hl : M.IsLimitOrdinal (L.eval ρ)) (level : Er_level_d (X.eval ρ) (L.eval ρ) V)
    (hκ : M.mem (κ.eval ρ) V) (ht : M.mem (t.eval ρ) V) :
    Formula.satisfies ρ (et_stretch_m ω κ L X F t D v) ↔
      Et_stretch_d hZF (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) (X.eval ρ) R (t.eval ρ) (D.eval ρ) (v.eval ρ) := by
  obtain ⟨P, hP, subsets⟩ := power K source.finite.mem_l
  obtain ⟨c, hm⟩ := source.code
  obtain ⟨c', j, ultra, next⟩ := it_ultra_exists_l hZF hm
    (loc.closed_limit_l hZFC source source closed (fun _ _ _ _ _ _ => Iff.rfl) hP subsets)
  obtain ⟨N, S, _, hn, _⟩ := next.mem_l hZF (ultra.target_mem_l hZF)
  have family := loc.measures_l hZF source.omega (source.read_source_l hZF) source.code source.theory
    (sf_finite_power_l hZF source.omega source.transitive source.code source.theory (source.finite_l (ZF.modelsKP hZF)) hP subsets)
  obtain ⟨_, _, hL, hF, _⟩ := loc
  exact et_stretch_sat_l hZF ρ ω κ L X F t D v source power family hm hn ultra hL hF hl level hκ ht

variable {T : M.Domain} (hT : M.TransitiveSet T) (nt : Nonempty {x // M.mem x T})
local notation "N₀" => rt_model_l T nt

include hT in
theorem et_stretch_source_l {d K R V} (ρ : Env N₀ d) (ω κ L X F t D v : Term d)
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval ρ).val (κ.eval ρ).val K (X.eval ρ).val R)
    (closed : Sc_bounded_omega_closed_d I (ω.eval ρ).val (X.eval ρ).val R)
    (power : Sc_power_d (X.eval ρ).val)
    (loc : It_local_d I (ω.eval ρ).val (X.eval ρ).val R (κ.eval ρ).val (L.eval ρ).val (F.eval ρ).val)
    (hl : M.IsLimitOrdinal (L.eval ρ).val) (level : Er_level_d (X.eval ρ).val (L.eval ρ).val V)
    (hκ : M.mem (κ.eval ρ).val V) (ht : M.mem (t.eval ρ).val V) :
    Formula.satisfies ρ (et_stretch_m ω κ L X F t D v) ↔
      Et_stretch_d hZF (ω.eval ρ).val (κ.eval ρ).val (L.eval ρ).val (F.eval ρ).val
        (X.eval ρ).val R (t.eval ρ).val (D.eval ρ).val (v.eval ρ).val := by
  have read := et_stretch_closed_l hZFC (K := K) (R := R) (V := V)
    (image_env_l (M := N₀) (N := M) Subtype.val ρ) ω κ L X F t D v
  simp only [eval_image_env_l (M := N₀) (N := M) Subtype.val ρ] at read
  exact (rt_model_delta_l hT nt (et_stretch_delta_l ..) ρ).trans
    (read source closed power loc hl level hκ ht)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原扩展器检验与完整类型伸展的合并读取

任意通过检验的候选扩展器都自动产生良基超幂。支撑的源内不可达性在
实际 Vδ 中向上读取，再构造秩层枚举；κ 型的整个查询域给出类型的秩界。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def et_quality_m {d} (ω κ L X F t D v : Term d) : Formula 1 d :=
  .conj (ex_quality_m ω κ L X F) (et_stretch_m ω κ L X F t D v)
derive_free_closed et_quality_m

theorem et_quality_delta_l {d} (ω κ L X F t D v : Term d) : (et_quality_m ω κ L X F t D v).IsDelta0 :=
  .conj (ex_quality_delta_l ..) (et_stretch_delta_l ..)

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem et_quality_sat_l {d δ K R n B U Q} (ρ : Env M d) (ω κ L X F t D v : Term d)
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval ρ) (κ.eval ρ) K (X.eval ρ) R)
    (hX : V_d I δ (X.eval ρ)) (hδ : M.IsLimitOrdinal δ) (hκL : M.mem (κ.eval ρ) (L.eval ρ))
    (hn : M.mem n (ω.eval ρ)) (hB : V_d I (κ.eval ρ) B)
    (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ.eval ρ)
    (pool : Tt_pool_d I (ω.eval ρ) n U Q) (type : M.MemberSubset (t.eval ρ) Q) :
    Formula.satisfies ρ (et_quality_m ω κ L X F t D v) ↔
      It_local_d I (ω.eval ρ) (X.eval ρ) R (κ.eval ρ) (L.eval ρ) (F.eval ρ) ∧
      Sc_inaccessible_d (ω.eval ρ) (X.eval ρ) (L.eval ρ) ∧
      Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (X.eval ρ) (F.eval ρ) ∧
      Et_stretch_d hZF (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) (X.eval ρ) R (t.eval ρ) (D.eval ρ) (v.eval ρ) := by
  obtain ⟨c, model⟩ := source.code
  have read (loc : It_local_d I (ω.eval ρ) (X.eval ρ) R (κ.eval ρ) (L.eval ρ) (F.eval ρ))
      (inacc : Sc_inaccessible_d (ω.eval ρ) (X.eval ρ) (L.eval ρ)) :
      Formula.satisfies ρ (et_stretch_m ω κ L X F t D v) ↔
        Et_stretch_d hZF (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) (X.eval ρ) R (t.eval ρ) (D.eval ρ) (v.eval ρ) := by
    obtain ⟨above, regular, strong⟩ := sc_v_inaccessible_up_l (ZF.modelsKP hZF) hδ hX inacc
    have hLX : M.mem (L.eval ρ) (X.eval ρ) := by obtain ⟨_, _, h, _, _⟩ := loc; exact h
    have hLδ := ZF.v_ordinal_height_l hZF hX regular.isCardinal.1 hLX
    obtain ⟨V, hV⟩ := ZF.v_exists_l I hZF regular.isCardinal.1
    have hUV := tt_constants_rank_l hZF hV regular.isLimitOrdinal hκL hB constants
    have hQV := pool.rank_mem_l (ZF.modelsKP hZF) source.omega hV regular.isLimitOrdinal
      (ZF.v_ordinal_mem_l I hZF hV above) hn hUV
    exact et_stretch_closed_l hZFC ρ ω κ L X F t D v source
      (sc_v_bounded_omega_closed_l (ZF.modelsKP hZF) source.omega hδ hX source.omega_mem model) (sc_v_power_l (ZF.modelsKP hZF) hδ hX) loc regular.isLimitOrdinal
      (ep_relative_rank_l hZFC source hX hδ hLδ above regular strong hV)
      (ZF.v_ordinal_mem_l I hZF hV hκL) (v_subset_mem_l I hV hQV type)
  rw [et_quality_m, Formula.satisfies_conj_iff, ex_quality_sat_l (ZF.modelsKP hZF) ρ ω κ L X F source]
  exact ⟨fun ⟨⟨loc, inacc, strength⟩, h⟩ => ⟨loc, inacc, strength, (read loc inacc).mp h⟩,
    fun ⟨loc, inacc, strength, h⟩ => ⟨⟨loc, inacc, strength⟩, (read loc inacc).mpr h⟩⟩

theorem et_quality_source_l {T : M.Domain} (hT : M.TransitiveSet T) (nt : Nonempty {x // M.mem x T})
    {d δ K R n B U Q} (ρ : Env (rt_model_l T nt) d) (ω κ L X F t D v : Term d)
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval ρ).val (κ.eval ρ).val K (X.eval ρ).val R)
    (hX : V_d I δ (X.eval ρ).val) (hδ : M.IsLimitOrdinal δ) (hκL : M.mem (κ.eval ρ).val (L.eval ρ).val)
    (hn : M.mem n (ω.eval ρ).val) (hB : V_d I (κ.eval ρ).val B)
    (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = (κ.eval ρ).val)
    (pool : Tt_pool_d I (ω.eval ρ).val n U Q) (type : M.MemberSubset (t.eval ρ).val Q) :
    Formula.satisfies ρ (et_quality_m ω κ L X F t D v) ↔
      It_local_d I (ω.eval ρ).val (X.eval ρ).val R (κ.eval ρ).val (L.eval ρ).val (F.eval ρ).val ∧
      Sc_inaccessible_d (ω.eval ρ).val (X.eval ρ).val (L.eval ρ).val ∧
      Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval ρ).val (κ.eval ρ).val (L.eval ρ).val (X.eval ρ).val (F.eval ρ).val ∧
      Et_stretch_d hZF (ω.eval ρ).val (κ.eval ρ).val (L.eval ρ).val (F.eval ρ).val
        (X.eval ρ).val R (t.eval ρ).val (D.eval ρ).val (v.eval ρ).val := by
  have read := et_quality_sat_l hZFC (δ := δ) (K := K) (R := R) (n := n) (B := B) (U := U) (Q := Q)
    (image_env_l (M := rt_model_l T nt) (N := M) Subtype.val ρ) ω κ L X F t D v
  simp only [eval_image_env_l (M := rt_model_l T nt) (N := M) Subtype.val ρ] at read
  exact (rt_model_delta_l hT nt (et_quality_delta_l ..) ρ).trans (read source hX hδ hκL hn hB constants pool type)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 弹性中的一个任意目标高度

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
    It_local_d I ω X R κ L F ∧ Sc_inaccessible_d ω X L ∧ Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X F ∧
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
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ.val K Z.val R) (hZ : V_d I δ.val Z.val)
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
  have trans := v_transitive_l I hY
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
      It_local_d I ω Z.val R κ.val L.val F.val ∧ Sc_inaccessible_d ω Z.val L.val ∧
        Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω κ.val L.val Z.val F.val ∧ Et_stretch_d hZF ω κ.val L.val F.val Z.val R t.val D.val v.val :=
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
    have hD := hp.rank_mem_l (ZF.modelsKP hZF) hω hZ hδ (ZF.v_ordinal_mem_l I hZF hZ hωδ) hn hU
    have hV := v_subset_mem_l I hZ hD (fun p pp => ((hv p).mp pp).1)
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
    {K R B U Q c S s : M.Domain} (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω (κ.eval ρ).val K (Z.eval ρ).val R)
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

/-! ## 同一元组的全高度弹性公式

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
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ.val K X R) (hX : V_d I δ.val X)
    (hδ : M.IsLimitOrdinal δ.val) (hωδ : M.mem ω δ.val) (hκδ : M.mem κ.val δ.val)
    (hm : Smem_d I c A S) (hn : M.mem n.val ω) (tuple : Fn0_d n.val A s) (point : M.mem δ.val A)
    (agree : Sx_graph_d I K₀ s h.val) :
    ee_realized_s.denote (⟨Fin.cases n (Fin.cases δ (Fin.cases κ (fun _ => ⟨ω, hωY⟩))),
      fun _ => h⟩ : Env N₀ 4) h ↔ Ee_realized_d hZF ω κ.val δ.val n.val s c X R := by
  let ρ := (⟨Fin.cases n (Fin.cases δ (Fin.cases κ (fun _ => ⟨ω, hωY⟩))), fun _ => h⟩ : Env N₀ 4).push h
  have trans := v_transitive_l I hY
  obtain ⟨B, U, hb, hu, constants⟩ := tt_constants_exists_l hZF hX hδ hκδ
  obtain ⟨D, pool⟩ := tt_pool_exists_l I hZF hω n.val U
  have hD := pool.rank_mem_l (ZF.modelsKP hZF) hω hX hδ source.omega_mem hn hu
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
    have ht := v_subset_mem_l I hX hD (fun p pp => ((truth p).mp pp).1)
    let q : (N₀).Domain := ⟨t, trans X Z.property t ht⟩
    exact ⟨Z, (rt_fp_v_l I hZF hω hY hωY δ Z).mpr hX, q, ht,
      (types Z q).mpr truth, (all Z q rfl truth).mpr steps⟩

include hω hA hY hs in
theorem ee_realized_source_l {d} (ρ : Env N₀ d) (w κ δ n h : Term d) (hw : w.eval ρ = ⟨ω, hωY⟩)
    {K X R c S s : M.Domain} (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω (κ.eval ρ).val K X R)
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

/-! ## 全高度弹性的实际内部程序

ZF 中按内部元数构造原程序；原变量先自动打包，源与类型都在公式内绑定。
语义读取中的 ZFC 用于实际超幂及支撑层枚举，不参与程序构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K₀" => fp_interpretation_l (ZF.models_kpi_l hZF)

private theorem st_ee_slots_l {ω w v d e b n : M.Domain} (hω : M.IsOmega ω) (hb : M.mem b ω)
    (hw : M.mem w b) (hv : M.mem v b) (hd : M.mem d b) (he : M.mem e b)
    (hn : M.mem n ω) (hnb : M.MemberSubset n b) :
    ∃ a m G u, Sformula_d Q ω a m G u ∧ ∀ (hZFC : M.Models ZFC) ν μ X Y Z c R c' R' κ δ K S s f,
      V_d Q ν X → V_d Q μ Y → M.SuccessorOf μ ν → V_d Q δ Z → M.IsLimitOrdinal δ →
      M.mem ω δ → M.mem κ δ → Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z S → Smem_d Q c X R → Smem_d Q c' Y R' →
      Fn0_d n X s → M.mem δ X → M.IsSetFunctionFromTo Q f ω Y →
      (∀ i x, M.mem i n → (M.PairMember Q i x s ↔ M.PairMember Q i x f)) →
      M.PairMember Q w ω f → M.PairMember Q v n f → M.PairMember Q d δ f → M.PairMember Q e κ f →
        (Satisfies_d Q ω c' a f ↔ Ee_realized_d (ZFC.models_zf_l hZFC) ω κ δ n s c Z S) := by
  let φ : Formula 1 5 := ee_realized_m (.bound 4) (.bound 1) (.bound 2) (.bound 3) .newest
  obtain ⟨a, m, G, u, form, compile⟩ := st_tuple_bind_l hZF hω hb hw hv hn hnb φ
    (ee_realized_closed_l _ _ _ _ _ rfl rfl rfl rfl rfl)
    (Fin.cases e (Fin.cases d (Fin.cases v (fun _ => w)))) (Fin.cases he (Fin.cases hd (Fin.cases hv (fun _ => hw))))
  refine ⟨a, m, G, u, form, fun hZFC ν μ X Y Z c R c' R' κ δ K S s f hV hW hs hZ hδ hωδ hκδ
    source lower upper fs point fn orig fw fv fd fe => ?_⟩
  have hωY := fn.output_mem_of_pairMember fw
  have sfn := fn0_function_l (ZF.modelsKP hZF) fs
  let ρ : Env (smdl_structure_l Q (R := R') upper.1.2.1) 4 :=
    ⟨Fin.cases ⟨κ, fn.output_mem_of_pairMember fe⟩ (Fin.cases ⟨δ, fn.output_mem_of_pairMember fd⟩
      (Fin.cases ⟨n, fn.output_mem_of_pairMember fv⟩ (fun _ => ⟨ω, hωY⟩))), fun _ => ⟨ω, hωY⟩⟩
  have graph h (hh : M.IsSetFunctionFromTo K₀ h n X)
      (same : ∀ i x, M.mem i n → (M.PairMember K₀ i x h ↔ M.PairMember Q i x f)) : Sx_graph_d Q K₀ s h :=
    fun i x => ⟨fun hx => (orig i x (hh.input_mem_of_pairMember hx)).mpr ((same i x (hh.input_mem_of_pairMember hx)).mp hx),
      fun hx => (same i x (sfn.input_mem_of_pairMember hx)).mpr ((orig i x (sfn.input_mem_of_pairMember hx)).mp hx)⟩
  have atom (h : (smdl_structure_l Q (R := R') upper.1.2.1).Domain) (same : Sx_graph_d Q K₀ s h.val) :
      Formula.satisfies (ρ.push h) φ ↔ Ee_realized_d (ZFC.models_zf_l hZFC) ω κ δ n s c Z S := by
    let η : Env (rt_model_l Y ⟨⟨ω, hωY⟩⟩) 5 := ⟨(ρ.push h).bound, (ρ.push h).free⟩
    exact (smem_formula_l Q upper _ φ η).symm.trans (ee_realized_source_l hZFC hω hV hW hs hωY η
      (.bound 4) (.bound 1) (.bound 2) (.bound 3) .newest rfl source hZ hδ hωδ hκδ lower hn fs point same)
  refine (compile ν μ X Y c' R' f upper ρ hV hW hs hωY fn fw fv
    (Fin.cases fe (Fin.cases fd (Fin.cases fv (fun _ => fw))))).trans ⟨?_, ?_⟩
  · rintro ⟨h, hh, same, truth⟩
    exact (atom h (graph h.val hh same)).mp truth
  · intro truth
    obtain ⟨h, hh, same⟩ := fn_recode_l Q K₀ hZF sfn
    have hδν := ZF.v_ordinal_height_l hZF hV hδ.1 point
    have hων := fun i hi => (v_ordinal_l Q hV).transitive δ hδν i (hδ.1.transitive ω hωδ i hi)
    have hHY := (ZF.v_successor_l Q hZF hV hW hs h).mpr (fp_function_rank_l Q hZF hω hV hων
      (fun i hi => ZF.v_ordinal_mem_l Q hZF hV (hων i (hω.transitive (ZF.modelsKP hZF) n hn i hi))) hh)
    exact ⟨⟨h, hHY⟩, hh, fun i x hi => (same i x).trans (orig i x hi), (atom ⟨h, hHY⟩ same).mpr truth⟩

/-- 构造只依赖内部 n；同一个原程序在全部合法后继秩层中精确读取全高度条件。 -/
theorem st_ee_build_l {ω n : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω) :
    ∃ v d e a m G u, M.SuccessorOf v n ∧ M.SuccessorOf d v ∧ M.SuccessorOf e d ∧ Sformula_d Q ω a m G u ∧
      ∀ (hZFC : M.Models ZFC) ν μ X Y Z c R c' R' κ δ K S s f,
      V_d Q ν X → V_d Q μ Y → M.SuccessorOf μ ν → V_d Q δ Z → M.IsLimitOrdinal δ →
      M.mem ω δ → M.mem κ δ → Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z S → Smem_d Q c X R → Smem_d Q c' Y R' →
      Fn0_d n X s → M.mem δ X → M.IsSetFunctionFromTo Q f ω Y →
      (∀ i x, M.mem i n → (M.PairMember Q i x s ↔ M.PairMember Q i x f)) →
      M.PairMember Q n ω f → M.PairMember Q v n f → M.PairMember Q d δ f → M.PairMember Q e κ f →
        (Satisfies_d Q ω c' a f ↔ Ee_realized_d (ZFC.models_zf_l hZFC) ω κ δ n s c Z S) := by
  obtain ⟨v, hv, hvω⟩ := hω.1.2 n hn
  obtain ⟨d, hd, hdω⟩ := hω.1.2 v hvω
  obtain ⟨e, he, heω⟩ := hω.1.2 d hdω
  obtain ⟨b, hb, hbω⟩ := hω.1.2 e heω
  have de := (hω.members_areOrdinals (ZF.modelsKP hZF) e heω).transitive d he.predecessor_mem
  have vd := (hω.members_areOrdinals (ZF.modelsKP hZF) d hdω).transitive v hd.predecessor_mem
  have eb := (hω.members_areOrdinals (ZF.modelsKP hZF) b hbω).transitive e hb.predecessor_mem
  have nb := eb n (de n (vd n hv.predecessor_mem))
  obtain ⟨a, m, G, u, form, read⟩ := st_ee_slots_l hZF hω hbω nb (eb v (de v hd.predecessor_mem))
    (eb d he.predecessor_mem) hb.predecessor_mem hn ((hω.members_areOrdinals (ZF.modelsKP hZF) b hbω).transitive n nb)
  exact ⟨v, d, e, a, m, G, u, hv, hd, he, form, read⟩

def Ee_stretch_read_d (ω n v d e z : M.Domain) : Prop := ∀ ν μ X Y Z c R c' R' κ δ K S s f,
    V_d Q ν X → V_d Q μ Y → M.SuccessorOf μ ν → V_d Q δ Z → M.IsLimitOrdinal δ →
    M.mem ω δ → M.mem κ δ → Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z S → Smem_d Q c X R → Smem_d Q c' Y R' →
    Fn0_d n X s → M.mem δ X → M.IsSetFunctionFromTo Q f ω Y →
    (∀ i x, M.mem i n → (Rd_entry_d i x s ↔ Rd_entry_d i x f)) →
    Rd_entry_d n ω f → Rd_entry_d v n f → Rd_entry_d d δ f → Rd_entry_d e κ f →
      (Sc_sat_d Q ω c' z f ↔ Ee_realized_d hZF ω κ δ n s c Z S)

/-- 伸展程序的自由参数全是内部自然数；κ、δ 及赋值只在读取时代入。 -/
structure Ee_stretch_program_d (ω n v d e z : M.Domain) : Prop where
  finite : M.mem n ω
  next_finite : M.mem v ω
  point_finite : M.mem d ω
  critical_finite : M.mem e ω
  natural : M.mem z ω
  next : M.SuccessorOf v n
  point : M.SuccessorOf d v
  critical : M.SuccessorOf e d
  read : ∀ hZFC : M.Models ZFC, Ee_stretch_read_d (ZFC.models_zf_l hZFC) ω n v d e z

include hZF in
theorem ee_stretch_program_l {ω n : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω) :
    ∃ v d e z, Ee_stretch_program_d ω n v d e z := by
  obtain ⟨v, d, e, a, m, G, u, hv, hd, he, form, compile⟩ := st_ee_build_l hZF hω hn
  obtain ⟨z, code⟩ := sc_num_exists_l Q hZF hω form
  have finite {a b} (ha : M.mem a ω) (succ : M.SuccessorOf b a) : M.mem b ω := by
    obtain ⟨b', hb', hbω⟩ := hω.1.2 a ha
    exact Structure.SuccessorOf.eq hZF.1 hb' succ ▸ hbω
  exact ⟨v, d, e, z, hn, finite hn hv, finite (finite hn hv) hd, finite (finite (finite hn hv) hd) he,
    sc_num_natural_l Q hZF hω code, hv, hd, he,
    fun hZFC ν μ X Y Z c R c' R' κ δ K S s f hX hY succ hZ hδ hwδ hkδ source lower upper tuple point fn old hw hn hd he =>
      (sc_sat_decode_l Q hZF hω code).trans
        (compile hZFC ν μ X Y Z c R c' R' κ δ K S s f hX hY succ hZ hδ hwδ hkδ source lower upper tuple point fn old hw hn hd he)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 全高度条件成为原 κ 型的一个固定查询

查询在任何类型和实现元组出现之前实际构造。名字列只使用原变量、指定
常量 δ 及 Vκ∪{κ} 中已有的常量；原 κ 型和原元组图都不是新参数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ee_stretch_program_d.query_l {ω κ n U D v d e z p : M.Domain} (hω : M.IsOmega ω)
    (program : Ee_stretch_program_d ω n v d e z) (pool : Tt_pool_d I ω n U D)
    (code : Ee_stretch_code_d ω n κ v d e z p) (hpD : M.mem p D) :
    ∀ (hZFC : M.Models ZFC) ν μ A Y X c R c' R' δ K S s t,
      V_d I ν A → V_d I μ Y → M.SuccessorOf μ ν → V_d I δ X → M.IsLimitOrdinal δ →
      M.mem ω δ → M.mem κ δ → Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X S → Smem_d I c A R → Smem_d I c' Y R' →
      Tt_realized_d I ω c' Y R' n s δ U D t → Fn0_d n A s → M.mem δ A →
        (M.mem p t ↔ Ee_realized_d (ZFC.models_zf_l hZFC) ω κ δ n s c X S) := by
  obtain ⟨C, kw, kn, kk, pair, hw, hnn, hk, old, cw, cn, cd, ck⟩ := code
  obtain ⟨N, E, names, seq, prod⟩ := pool
  obtain ⟨z', _, C', hC', pair'⟩ := (prod p).mp hpD
  obtain ⟨eqz, eqC⟩ := kpair_injective_l M pair' pair
  subst z' C'
  obtain ⟨b, hbω, cf⟩ := (seq C).mp hC'
  intro hZFC ν μ A Y X c R c' R' δ K S s t hA hY succ hX hδ hωδ hκδ source lower upper type tuple point
  obtain ⟨r, assign, fr⟩ := tn_assign_exists_l hZF (hω.members_areOrdinals (ZF.modelsKP hZF) n program.finite)
    type.tuple type.point type.constants names (fn0_of_function_l (ZF.modelsKP hZF) cf)
  obtain ⟨f, fill, ff⟩ := senv_fill_exists_l I hZF (fn0_function_l (ZF.modelsKP hZF) fr) type.point
  have value i q x (hc : Rd_entry_d i q C) (val : Tn_value_d n s δ q x) : Rd_entry_d i x f :=
    (fill.2 i x).mpr ⟨hω.transitive (ZF.modelsKP hZF) b hbω i (cf.input_mem_of_pairMember hc),
      Or.inl ⟨cf.input_mem_of_pairMember hc, (assign.2 i x).mpr ⟨q, hc, val⟩⟩⟩
  have vars i x (hx : Rd_entry_d i x s) : Rd_entry_d i x f :=
    value i i x (old i (type.tuple.bound_l hx).1) (Or.inl hx)
  have same i x (hi : M.mem i n) : Rd_entry_d i x s ↔ Rd_entry_d i x f := by
    refine ⟨vars i x, fun hx => ?_⟩
    obtain ⟨y, _, hy⟩ := type.tuple.2.1 i hi
    exact (ff.1.2 i y x (vars i y hy) hx) ▸ hy
  exact (type.truth p).trans ((and_iff_right hpD).trans
    ((tt_query_decode_l I (ZF.modelsKP hZF) pair program.natural hbω cf.2.1 assign fill).trans
        (program.read hZFC ν μ A Y X c R c' R' κ δ K S s f hA hY succ hX hδ hωδ hκδ source lower upper tuple point ff same
          (value n kw ω cw (Or.inr (Or.inr hw))) (value v kn n cn (Or.inr (Or.inr hnn)))
          (value d n δ cd (Or.inr (Or.inl ⟨rfl, rfl⟩))) (value e kk κ ck (Or.inr (Or.inr hk))))))

/-- 同一程序生成查询，原自然数码和名字列随语义读取一起返回。 -/
theorem ee_query_build_l {ω κ n B U D : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω)
    (hκ : M.IsLimitOrdinal κ) (hB : V_d I κ B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ)
    (pool : Tt_pool_d I ω n U D) : ∃ p v d e z,
      Ee_stretch_program_d ω n v d e z ∧ Ee_stretch_code_d ω n κ v d e z p ∧ M.mem p D ∧
      ∀ (hZFC : M.Models ZFC) ν μ A Y X c R c' R' δ K S s t,
      V_d I ν A → V_d I μ Y → M.SuccessorOf μ ν → V_d I δ X → M.IsLimitOrdinal δ →
      M.mem ω δ → M.mem κ δ → Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X S → Smem_d I c A R → Smem_d I c' Y R' →
      Tt_realized_d I ω c' Y R' n s δ U D t → Fn0_d n A s → M.mem δ A →
        (M.mem p t ↔ Ee_realized_d (ZFC.models_zf_l hZFC) ω κ δ n s c X S) := by
  obtain ⟨v, d, e, z, program⟩ := ee_stretch_program_l hZF hω hn
  obtain ⟨N, E, names, seq, prod⟩ := pool
  obtain ⟨hωU, hnU⟩ := tt_constants_finite_l hZF hω hn hκ hB constants
  obtain ⟨b, C, kw, kn, kk, _, hbω, cf, hw, hnn, hk, old, cw, cn, cd, ck⟩ :=
    ee_column_l hZF hω hn program.next program.point program.critical hωU hnU ((constants κ).mpr (Or.inr rfl)) names
  obtain ⟨p, pair⟩ := (I).total z C
  have hpD := (prod p).mpr ⟨z, program.natural, C, (seq C).mpr ⟨b, hbω, cf⟩, pair⟩
  have code : Ee_stretch_code_d ω n κ v d e z p := ⟨C, kw, kn, kk, pair, hw, hnn, hk, old, cw, cn, cd, ck⟩
  exact ⟨p, v, d, e, z, program, code, hpD, program.query_l hZF hω ⟨N, E, names, seq, prod⟩ code hpD⟩

end YesMetaZFC.SetTheory.LargeCardinal
