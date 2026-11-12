-- Pandoc recognizes AMS theorem bodies and styles, but leaves their \label
-- commands raw and numbers each fragment from one. Recover only these known
-- semantics before applying the strict raw-TeX check below.
local environments = {
  theorem = {"Theorem", "theorem"}, thm = {"Theorem", "theorem"},
  proposition = {"Proposition", "proposition"}, prop = {"Proposition", "proposition"},
  lemma = {"Lemma", "lemma"}, lem = {"Lemma", "lemma"},
  corollary = {"Corollary", "corollary"}, cor = {"Corollary", "corollary"},
  definition = {"Definition", "definition"}, defn = {"Definition", "definition"},
  example = {"Example", "example"},
  remark = {"Remark", "remark"}, rem = {"Remark", "remark"},
}

local function theorem_blocks(doc)
  local prefix = doc.meta["theorem-prefix"]
  prefix = prefix and pandoc.utils.stringify(prefix) or nil
  return doc:walk({Div = function(div)
    local spec
    for _, class in ipairs(div.classes) do
      if environments[class] then spec = environments[class]; break end
    end
    if not spec then return nil end

    div:walk({RawInline = function(el)
      if (el.format == "latex" or el.format == "tex")
          and el.text:match("^\\phantomsection%s*$") then
        error("Use the theorem's opening label instead of a prose anchor inside its environment.")
      end
    end})

    local first = div.content[1]
    local heading = first and first.t == "Para" and first.content[1] or nil
    local ordinal = heading and (heading.t == "Strong" or heading.t == "Emph")
      and pandoc.utils.stringify(heading):match("^" .. spec[1] .. " (%d+)$") or nil
    if not ordinal then
      error("Unrecognized Pandoc theorem heading; check the shared theorem declarations.")
    end
    local number = prefix and prefix .. "." .. ordinal or ordinal
    heading.content = {pandoc.Str(spec[1]), pandoc.Space(), pandoc.Str(number)}
    first.content[1] = heading

    local label, display_seen
    first = first:walk({traverse = "topdown",
      Math = function(el)
        if el.mathtype == "DisplayMath" then display_seen = true end
      end,
      RawInline = function(el)
        if el.format ~= "latex" and el.format ~= "tex" then return nil end
        local target = el.text:match("^\\label%s*{([^{}%s]+)}%s*$")
        if not target then return nil end
        -- A label after a numbered display may refer to the equation instead.
        -- Require theorem labels in the opening paragraph before any display.
        if label or display_seen then
          error("Place one theorem label immediately after \\begin{...}[Title], before displays.")
        end
        label = target
        return {}
      end,
    })
    div.content[1] = first
    if label then
      if div.identifier ~= "" and div.identifier ~= label then
        error("Theorem environment has conflicting identifiers.")
      end
      div.identifier = label
    end
    div.classes:insert("theorem-block")
    if not div.classes:includes(spec[2]) then div.classes:insert(spec[2]) end
    return div
  end})
end

-- An explicit hyperref anchor preserves a prose link after removing a heading.
-- Accept only the paired commands: a bare label could otherwise inherit the
-- wrong PDF destination, and an unrelated raw command must still fail below.
local function prose_anchors(inlines)
  local result = pandoc.List()
  local index = 1
  while index <= #inlines do
    local el = inlines[index]
    if el.t == "RawInline" and (el.format == "latex" or el.format == "tex")
        and el.text:match("^\\phantomsection%s*$") then
      local following = index + 1
      while inlines[following] and
          (inlines[following].t == "Space" or inlines[following].t == "SoftBreak") do
        following = following + 1
      end
      local label = inlines[following]
      local target = label and label.t == "RawInline"
        and (label.format == "latex" or label.format == "tex")
        and label.text:match("^\\label%s*{([^{}%s]+)}%s*$") or nil
      if not target then
        error("A prose anchor must pair \\phantomsection immediately with \\label{semantic-id}.")
      end
      result:insert(pandoc.Span({}, pandoc.Attr(target, {"prose-anchor"})))
      index = following + 1
    else
      result:insert(el)
      index = index + 1
    end
  end
  return result
end

local function anchor_paragraph(para)
  for _, el in ipairs(para.content) do
    if el.t ~= "Space" and el.t ~= "SoftBreak" and
        not (el.t == "Span" and el.classes:includes("prose-anchor")) then
      return nil
    end
  end
  -- A stand-alone destination should not introduce a visible blank paragraph.
  return pandoc.Plain(para.content)
end

-- Pandoc expands user-defined math environments (including smallpmatrix) with
-- \bgroup/\egroup wrappers. MathJax needs literal grouping braces instead.
-- Preserve the groups, and read control sequences rather than replacing text:
-- in a matrix row break followed by "bgroup", the two backslashes are one token.
local function math_groups(el)
  local parts, index = {}, 1
  while index <= #el.text do
    local char = el.text:sub(index, index)
    if char ~= "\\" then
      parts[#parts + 1] = char
      index = index + 1
    else
      local word = el.text:sub(index + 1):match("^[A-Za-z]+")
      if word then
        parts[#parts + 1] = ({bgroup = "{", egroup = "}"})[word] or "\\" .. word
        index = index + #word + 1
      else
        parts[#parts + 1] = el.text:sub(index, index + 1)
        index = index + 2
      end
    end
  end
  el.text = table.concat(parts)
  return el
end

-- Number only explicitly labeled equation environments. The volume assembler
-- supplies chapter.section; the visible number is ordinary HTML, never a
-- MathJax counter whose value could depend on the page/tab rendering order.
local function equations(doc)
  local prefix = doc.meta["theorem-prefix"]
  prefix = prefix and pandoc.utils.stringify(prefix) or nil
  local ordinal = 0
  return doc:walk({Math = function(el)
    local body = el.text:match("^\\begin{equation}%s*(.-)%s*\\end{equation}$")
    if body then
      if not prefix then
        error("Define numbered equations in manuscript introductions or text.tex sections.")
      end
      local label, count
      body, count = body:gsub("\\label%s*{([^{}%s]+)}", function(target)
        label = target
        return ""
      end)
      if count ~= 1 then
        error("Each equation environment needs exactly one semantic \\label{...}.")
      end
      if body:match("\\tag") or body:match("\\notag") or body:match("\\nonumber")
          or body:match("\\eqref") or body:match("\\ref%s*{") then
        error("Equation numbers are automatic; put references in prose and omit tag/notag/nonumber.")
      end
      ordinal = ordinal + 1
      local number = prefix .. "." .. ordinal
      el.text = body
      local tag = pandoc.Span({pandoc.Str("(" .. number .. ")")},
                              pandoc.Attr("", {"equation-number"}))
      return pandoc.Span({el, tag}, pandoc.Attr(label, {"numbered-equation"},
                         {["data-equation-number"] = number}))
    end
    if el.text:match("\\label") or el.text:match("\\tag")
        or el.text:match("\\eqref") or el.text:match("\\ref%s*{")
        or el.text:match("\\begin{equation}") or el.text:match("\\begin{align}")
        or el.text:match("\\begin{gather}") or el.text:match("\\begin{multline}")
        or el.text:match("\\begin{eqnarray}") then
      error("Use a labeled equation (with aligned for multiple lines), and put \\eqref in prose.")
    end
  end, RawInline = function(el)
    if el.format ~= "latex" and el.format ~= "tex" then return nil end
    local label = el.text:match("^\\eqref%s*{([^{}%s]+)}%s*$")
    if label then
      -- Resolved against all manuscript equations after the volume is rendered,
      -- so forward references and references from Compare work as well.
      return pandoc.Link({pandoc.Str("?")}, "#" .. label, "",
                         pandoc.Attr("", {"equation-reference"}))
    end
  end})
end

-- Pandoc can silently drop raw LaTeX it cannot render. Make that an authoring error.
local function reject(el)
  error("Unsupported LaTeX in website conversion: " .. el.text ..
        "\nUse a Pandoc-supported construct or add a tested conversion rule.")
end
return {
  {Pandoc = theorem_blocks},
  {Inlines = prose_anchors},
  {Para = anchor_paragraph},
  {Math = math_groups},
  {Pandoc = equations},
  {RawBlock = reject, RawInline = reject},
}
