;;; wikimode.el --- side window browser for markdown wikis -*- lexical-binding: t; -*-

;;; Commentary:
;;
;; A persistent side window for browsing a project of markdown or org
;; files the way a jekyll blog or github wiki presents itself: a full
;; text search entry point, a sortable file list, and a tag list. For
;; markdown files, the title and tags come from jekyll-style YAML
;; frontmatter (`title:`, and `tags: [a, b]` or a `tags:` block list).
;; For org files, they come from the toplevel `#+title:' and
;; `#+filetags:' keywords. Either way, if no tags are found there,
;; tags are instead read from a "**Tags:** #foo #bar" line anywhere in
;; the body, if present.
;; Selecting a tag filters the file list down to files carrying that tag.
;;
;; Brainstormed in ~/org/wikimode.org.
;;
;; Entry point: `wikimode-toggle'.
;;
;; Key bindings inside the *wikimode* buffer:
;;   RET   open file at point / toggle tag filter / expand section / search
;;   TAB   expand or collapse the section at point
;;   /     full text search (via `consult-ripgrep') scoped to the project
;;   s     cycle file sort order (alphabetical / most recently modified)
;;   S     cycle tag sort order (alphabetical / by count)
;;   a     clear the active tag selection (which restricts the file list)
;;   f     filter the list at point (files by name/title, tags by name)
;;   F     clear the active filter for the section at point
;;   g     rescan the project for files and tags
;;   q     bury the window

;;; Code:

(require 'project)
(require 'seq)
(require 'cl-lib)

;; Forward declaration only, so `wikimode-search' can dynamically bind it
;; without forcing `consult' to load: `consult-ripgrep' is normally reached
;; via autoload, at which point this defcustom doesn't exist as a special
;; variable yet, so a plain `let' over it would silently be lexical instead
;; of dynamic and consult--ripgrep-make-builder would never see it.
(defvar consult-ripgrep-args)

(defgroup wikimode nil
  "Side window wiki browser for markdown projects."
  :group 'convenience)

(defcustom wikimode-file-extensions '("md" "markdown" "org")
  "File extensions (without the dot) that wikimode treats as wiki pages."
  :type '(repeat string)
  :group 'wikimode)

(defcustom wikimode-size 0.25
  "Width of the wikimode side window.
Either a positive integer (columns) or a fraction of the frame width."
  :type 'number
  :group 'wikimode)

(defcustom wikimode-position 'left
  "Side of the frame the wikimode window opens on."
  :type '(choice (const left) (const right))
  :group 'wikimode)

(defcustom wikimode-collapse-threshold 12
  "Maximum entries shown per section before it collapses behind an expander."
  :type 'integer
  :group 'wikimode)

(defface wikimode-current-file '((t :foreground "darkorange4" :weight extra-bold))
  "Face for the file currently shown in the main window."
  :group 'wikimode)

(defconst wikimode-buffer-name "*wikimode*"
  "Name of the wikimode side window buffer.")

;; State, buffer-local to the *wikimode* buffer.
(defvar-local wikimode--root nil)
(defvar-local wikimode--files nil)          ; all wiki files, relative to root
(defvar-local wikimode--file-tags nil)      ; hash: relative file -> (tags)
(defvar-local wikimode--tag-files nil)      ; hash: tag -> (relative file)
(defvar-local wikimode--file-titles nil)    ; hash: relative file -> frontmatter title
(defvar-local wikimode--file-sort 'alpha)   ; 'alpha | 'recent
(defvar-local wikimode--tag-sort 'alpha)    ; 'alpha | 'count
(defvar-local wikimode--tag-filter nil)     ; nil or an active tag string
(defvar-local wikimode--file-filter nil)    ; nil or an active file name/title substring
(defvar-local wikimode--tag-name-filter nil) ; nil or an active tag name substring
(defvar-local wikimode--files-expanded nil)
(defvar-local wikimode--tags-expanded nil)
(defvar-local wikimode--current-file nil) ; relative path of the file shown in the main window, or nil

;;; Frontmatter / tag parsing

(defun wikimode--frontmatter-lines (file)
  "Return the lines of FILE's YAML frontmatter, or nil if it has none."
  (when (file-readable-p file)
    (with-temp-buffer
      (insert-file-contents file nil 0 4096)
      (goto-char (point-min))
      (when (looking-at-p "---[ \t]*$")
        (forward-line 1)
        (let ((start (point)))
          (when (re-search-forward "^---[ \t]*$" nil t)
            (split-string (buffer-substring-no-properties start (line-beginning-position))
                          "\n")))))))

(defun wikimode--split-inline-tags (inline)
  "Split an inline tags value like \"[a, b]\" or \"a, b\" into a list."
  (let ((stripped (string-trim inline "\\[[ \t]*" "[ \t]*\\]")))
    (delete "" (mapcar (lambda (s) (string-trim s "[\"' \t]*" "[\"' \t]*"))
                        (split-string stripped ",")))))

(defun wikimode--collect-block-tags (lines)
  "Collect a YAML block list of tags (\"  - foo\") from the head of LINES."
  (let (tags)
    (while (and lines (string-match "\\`[ \t]*-[ \t]+\\(.*\\)\\'" (car lines)))
      (push (string-trim (match-string 1 (car lines)) "[\"']" "[\"']") tags)
      (setq lines (cdr lines)))
    (nreverse tags)))

(defun wikimode--parse-tags (lines)
  "Extract a list of tags from jekyll-style frontmatter LINES."
  (catch 'done
    (while lines
      (let ((line (pop lines)))
        (when (string-match "\\`tags:[ \t]*\\(.*\\)\\'" line)
          (let ((inline (string-trim (match-string 1 line))))
            (throw 'done
                   (if (not (string-empty-p inline))
                       (wikimode--split-inline-tags inline)
                     (wikimode--collect-block-tags lines)))))))
    nil))

(defun wikimode--parse-body-tags (file)
  "Extract tags from a \"**Tags:** #foo #bar\" line anywhere in FILE's body.
Return nil if FILE has no such line."
  (when (file-readable-p file)
    (with-temp-buffer
      (insert-file-contents file)
      (goto-char (point-min))
      (let ((case-fold-search t))
        (when (re-search-forward "^\\*\\*Tags:\\*\\*[ \t]*\\(.*\\)$" nil t)
          (let ((rest (match-string 1))
                tags)
            (while (string-match "#\\([[:alnum:]_-]+\\)" rest)
              (push (match-string 1 rest) tags)
              (setq rest (substring rest (match-end 0))))
            (nreverse tags)))))))

(defun wikimode--parse-title (lines)
  "Extract the title from jekyll-style frontmatter LINES.
Return nil if there is no title key or its value is empty."
  (catch 'done
    (dolist (line lines)
      (when (string-match "\\`title:[ \t]*\\(.*\\)\\'" line)
        (let ((title (string-trim (match-string 1 line) "[\"' \t]*" "[\"' \t]*")))
          (throw 'done (unless (string-empty-p title) title)))))
    nil))

(defun wikimode--org-p (file)
  "Return non-nil if FILE is an org file, by extension."
  (equal (downcase (or (file-name-extension file) "")) "org"))

(defun wikimode--parse-org-title (file)
  "Return FILE's toplevel \"#+title:\" value, or nil if absent/empty."
  (when (file-readable-p file)
    (with-temp-buffer
      (insert-file-contents file nil 0 4096)
      (goto-char (point-min))
      (let ((case-fold-search t))
        (when (re-search-forward "^#\\+title:[ \t]*\\(.*\\)$" nil t)
          (let ((title (string-trim (match-string 1))))
            (unless (string-empty-p title) title)))))))

(defun wikimode--parse-org-tags (file)
  "Return FILE's toplevel \"#+filetags:\" value as a list of tags, or nil."
  (when (file-readable-p file)
    (with-temp-buffer
      (insert-file-contents file nil 0 4096)
      (goto-char (point-min))
      (let ((case-fold-search t))
        (when (re-search-forward "^#\\+filetags:[ \t]*\\(.*\\)$" nil t)
          (delete "" (split-string (string-trim (match-string 1)) ":" t)))))))

(defun wikimode--file-tags-and-title (full)
  "Return (TAGS . TITLE) for FULL, dispatching on org vs. frontmatter format.
For org files, tags/title come from the toplevel \"#+filetags:\"/\"#+title:\"
keywords. For everything else, they come from YAML frontmatter. Either
way, if no tags are found there, fall back to a \"**Tags:** #foo #bar\"
line anywhere in the body."
  (if (wikimode--org-p full)
      (cons (or (wikimode--parse-org-tags full) (wikimode--parse-body-tags full))
            (wikimode--parse-org-title full))
    (let ((lines (wikimode--frontmatter-lines full)))
      (cons (or (wikimode--parse-tags lines) (wikimode--parse-body-tags full))
            (wikimode--parse-title lines)))))

;;; Project scanning

(defun wikimode--find-root ()
  "Return the root directory wikimode should scan."
  (if-let ((proj (project-current)))
      (project-root proj)
    default-directory))

(defun wikimode--extension-p (file)
  (let ((ext (file-name-extension file)))
    (and ext (member (downcase ext) wikimode-file-extensions))))

(defun wikimode--relative-current-file (root)
  "Return the file backing the current buffer, relative to ROOT.
Nil if the current buffer isn't visiting a wiki page under ROOT."
  (when-let* ((file (buffer-file-name))
              (root (and root (expand-file-name root)))
              ((file-in-directory-p file root))
              (rel (file-relative-name file root))
              ((wikimode--extension-p rel)))
    rel))

(defun wikimode--main-window-file (root)
  "Return the wiki page shown in the frame's main window, relative to ROOT."
  (let ((main (window-main-window)))
    (when (window-live-p main)
      (with-current-buffer (window-buffer main)
        (wikimode--relative-current-file root)))))

(defun wikimode--collect-files (root)
  "Return wiki page files under ROOT as paths relative to ROOT."
  (let* ((proj (project-current nil root))
         (all (if proj
                  (project-files proj)
                (directory-files-recursively
                 root ".*" nil
                 (lambda (dir) (not (string-match-p "\\.git\\'" dir)))))))
    (sort (mapcar (lambda (f) (file-relative-name f root))
                  (seq-filter #'wikimode--extension-p all))
          #'string-lessp)))

(defun wikimode--hash-keys (table)
  (let (keys)
    (maphash (lambda (k _v) (push k keys)) table)
    keys))

(defun wikimode--build-tag-tables (root files)
  "Return (file-tags tag-files file-titles) hash tables for FILES under ROOT."
  (let ((file-tags (make-hash-table :test 'equal))
        (tag-files (make-hash-table :test 'equal))
        (file-titles (make-hash-table :test 'equal)))
    (dolist (file files)
      (let* ((full (expand-file-name file root))
             (tags-and-title (wikimode--file-tags-and-title full))
             (tags (car tags-and-title))
             (title (cdr tags-and-title)))
        (when tags
          (puthash file tags file-tags)
          (dolist (tag tags)
            (puthash tag (cons file (gethash tag tag-files)) tag-files)))
        (when title
          (puthash file title file-titles))))
    (list file-tags tag-files file-titles)))

(defun wikimode-refresh (&optional root)
  "Rescan for wiki files and tags under ROOT.
ROOT defaults to `wikimode--find-root', which looks at the current
buffer -- callers refreshing on behalf of a different window (where
the wikimode buffer itself is current, not the window that triggered
the refresh) must pass ROOT explicitly instead of relying on that."
  (interactive)
  (unless (derived-mode-p 'wikimode-mode)
    (user-error "Not in a wikimode buffer"))
  (setq wikimode--root (or root (wikimode--find-root)))
  ;; Keep this buffer's notion of "here" in sync with the tracked project, so
  ;; that anything resolving a project from this buffer's directory (e.g. a
  ;; minibuffer opened while this buffer is current, or a `g' rescan) agrees
  ;; with `wikimode--root' instead of whatever directory was current when
  ;; this buffer was first created.
  (setq default-directory (file-name-as-directory wikimode--root))
  (setq wikimode--current-file (wikimode--main-window-file wikimode--root))
  (setq wikimode--files (wikimode--collect-files wikimode--root))
  (setq wikimode--tag-filter nil)
  (let ((tables (wikimode--build-tag-tables wikimode--root wikimode--files)))
    (setq wikimode--file-tags (nth 0 tables))
    (setq wikimode--tag-files (nth 1 tables))
    (setq wikimode--file-titles (nth 2 tables)))
  (wikimode--render))

;;; Sorting

(defun wikimode--file-matches-filter-p (file)
  (or (not wikimode--file-filter)
      (let ((case-fold-search t))
        (or (string-match-p (regexp-quote wikimode--file-filter)
                             (wikimode--file-display-name file))
            (string-match-p (regexp-quote wikimode--file-filter) file)))))

(defun wikimode--sorted-files ()
  (let ((files (if wikimode--tag-filter
                    (gethash wikimode--tag-filter wikimode--tag-files)
                  wikimode--files)))
    (setq files (seq-filter #'wikimode--file-matches-filter-p files))
    (pcase wikimode--file-sort
      ('recent (sort (copy-sequence files)
                     (lambda (a b)
                       (time-less-p
                        (file-attribute-modification-time
                         (file-attributes (expand-file-name b wikimode--root)))
                        (file-attribute-modification-time
                         (file-attributes (expand-file-name a wikimode--root)))))))
      (_ (sort (copy-sequence files) #'string-lessp)))))

(defun wikimode--tag-matches-filter-p (tag)
  (or (not wikimode--tag-name-filter)
      (let ((case-fold-search t))
        (string-match-p (regexp-quote wikimode--tag-name-filter) tag))))

(defun wikimode--tags-in-use ()
  "Return the tags actually present on the current set of files.
All tags in the project, unless `wikimode--file-filter' is active, in
which case only tags used by files matching that filter."
  (if wikimode--file-filter
      (let (tags)
        (dolist (file (seq-filter #'wikimode--file-matches-filter-p wikimode--files))
          (dolist (tag (gethash file wikimode--file-tags))
            (cl-pushnew tag tags :test #'equal)))
        tags)
    (wikimode--hash-keys wikimode--tag-files)))

(defun wikimode--sorted-tags ()
  (let ((tags (seq-filter #'wikimode--tag-matches-filter-p (wikimode--tags-in-use))))
    (pcase wikimode--tag-sort
      ('count (sort tags (lambda (a b)
                            (let ((ca (length (gethash a wikimode--tag-files)))
                                  (cb (length (gethash b wikimode--tag-files))))
                              (if (= ca cb) (string-lessp a b) (> ca cb))))))
      (_ (sort tags #'string-lessp)))))

;;; Rendering

(defun wikimode--insert-list-section (title section entries expanded render-fn &optional filter-info)
  "Insert a collapsible list SECTION (a symbol) with heading TITLE.
ENTRIES is the full list to show; if longer than
`wikimode-collapse-threshold' and not EXPANDED, only the head is shown,
preceded by an expander line.  RENDER-FN is called with each entry and
inserts its line. FILTER-INFO, if non-nil, is inserted as its own
status line directly below TITLE, describing the active filter(s)."
  ;; The trailing "\n" of each line below is included in its `propertize'
  ;; call (or explicitly extended, for entry lines) so that hotkeys still
  ;; detect the right properties when point sits at end-of-line: `(point)'
  ;; there is the position of the newline character itself, and
  ;; `get-text-property' looks at the character *after* point.
  (insert (propertize (concat title "\n") 'face 'bold 'wikimode-section section))
  (when filter-info
    (let ((indented (mapconcat (lambda (line) (concat "  " line))
                                (split-string filter-info "\n") "\n")))
      (insert (propertize (concat indented "\n") 'face 'bold 'wikimode-section section))))
  (let* ((total (length entries))
         (visible (if (or expanded (<= total wikimode-collapse-threshold))
                      entries
                    (seq-take entries wikimode-collapse-threshold))))
    (when (> total wikimode-collapse-threshold)
      (insert (propertize (concat (if expanded
                                       "▼ collapse"
                                     (format "▶ %d more" (- total wikimode-collapse-threshold)))
                                   "\n")
                           'face 'shadow
                           'wikimode-section section
                           'wikimode-toggle section)))
    (dolist (entry visible)
      (let ((start (point)))
        (funcall render-fn entry)
        (let ((end (point)))
          (insert "\n")
          ;; Extend the entry's own properties (`wikimode-file'/`wikimode-tag',
          ;; `face', ...) from its last character onto the newline too.
          (when (> end start)
            (set-text-properties end (point) (text-properties-at (1- end)))))
        (put-text-property start (point) 'wikimode-section section)))))

(defun wikimode--file-display-name (file)
  "Return the display name for FILE.
Its frontmatter title if present, otherwise its filename without
the extension."
  (or (and wikimode--file-titles (gethash file wikimode--file-titles))
      (file-name-sans-extension (file-name-nondirectory file))))

(defun wikimode--insert-file-line (file)
  (insert (propertize (wikimode--file-display-name file)
                       'wikimode-file file
                       'face (and (equal file wikimode--current-file)
                                  'wikimode-current-file))))

(defun wikimode--insert-tag-line (tag)
  (let ((count (length (gethash tag wikimode--tag-files)))
        (active (equal tag wikimode--tag-filter)))
    (insert (propertize (format "%s%s (%d)" (if active "* " "  ") tag count)
                         'wikimode-tag tag))))

(defun wikimode--render ()
  "Redraw the wikimode buffer from its current state."
  (let ((inhibit-read-only t)
        (line (line-number-at-pos)))
    (erase-buffer)
    (insert (propertize "Full Text Search" 'face 'bold) "\n")
    (insert (propertize "[ / to search ]\n" 'face 'shadow 'wikimode-search t) "\n")
    (wikimode--insert-list-section
     (format "Files (%s)" (if (eq wikimode--file-sort 'recent) "recent" "alphabetical"))
     'files (wikimode--sorted-files) wikimode--files-expanded
     #'wikimode--insert-file-line
     (let ((parts (delq nil (list (and wikimode--tag-filter (format "tag: %s" wikimode--tag-filter))
                                   (and wikimode--file-filter (format "filter: %s" wikimode--file-filter))))))
       (and parts (mapconcat #'identity parts "\n"))))
    (insert "\n")
    (wikimode--insert-list-section
     (format "Tags (%s)" (if (eq wikimode--tag-sort 'count) "by count" "alphabetical"))
     'tags (wikimode--sorted-tags) wikimode--tags-expanded
     #'wikimode--insert-tag-line
     (and wikimode--tag-name-filter (format "filter: %s" wikimode--tag-name-filter)))
    (goto-char (point-min))
    (forward-line (1- line)))
  (force-mode-line-update))

;;; Commands

(defun wikimode-toggle-section ()
  "Expand or collapse the section at point."
  (interactive)
  (pcase (get-text-property (point) 'wikimode-section)
    ('files (setq wikimode--files-expanded (not wikimode--files-expanded)))
    ('tags (setq wikimode--tags-expanded (not wikimode--tags-expanded)))
    (_ (user-error "No section at point")))
  (wikimode--render))

(defun wikimode-clear-tag-filter ()
  "Clear the active tag filter, if any."
  (interactive)
  (setq wikimode--tag-filter nil)
  (wikimode--render))

(defun wikimode-filter-section ()
  "Filter the list in the section at point to items matching a substring.
In the Files section this matches file titles/names; in the Tags
section it matches tag names."
  (interactive)
  (pcase (get-text-property (point) 'wikimode-section)
    ('files (let ((filter (string-trim (read-string "Filter files: " wikimode--file-filter))))
              (setq wikimode--file-filter (unless (string-empty-p filter) filter))))
    ('tags (let ((filter (string-trim (read-string "Filter tags: " wikimode--tag-name-filter))))
             (setq wikimode--tag-name-filter (unless (string-empty-p filter) filter))))
    (_ (user-error "No filterable section at point")))
  (wikimode--render))

(defun wikimode-clear-section-filter ()
  "Clear the active substring filter for the section at point."
  (interactive)
  (pcase (get-text-property (point) 'wikimode-section)
    ('files (setq wikimode--file-filter nil))
    ('tags (setq wikimode--tag-name-filter nil))
    (_ (user-error "No filterable section at point")))
  (wikimode--render))

(defun wikimode-cycle-file-sort ()
  "Cycle the file list between alphabetical and most-recently-modified order."
  (interactive)
  (setq wikimode--file-sort (if (eq wikimode--file-sort 'alpha) 'recent 'alpha))
  (wikimode--render))

(defun wikimode-cycle-tag-sort ()
  "Cycle the tag list between alphabetical and by-count order."
  (interactive)
  (setq wikimode--tag-sort (if (eq wikimode--tag-sort 'alpha) 'count 'alpha))
  (wikimode--render))

(defun wikimode--select-main-window ()
  "Select the frame's main editing window, as opposed to a side window."
  (let ((main (window-main-window)))
    (when (window-live-p main)
      (select-window main))))

(defun wikimode-search ()
  "Full text search the project, opening matches in the main window.
Restricted to files with one of `wikimode-file-extensions'."
  (interactive)
  (unless (fboundp 'consult-ripgrep)
    (user-error "consult-ripgrep is not available"))
  (let ((root wikimode--root)
        (consult-ripgrep-args
         (append (ensure-list (bound-and-true-p consult-ripgrep-args))
                 (mapcar (lambda (ext) (format "--glob=*.%s" ext))
                         wikimode-file-extensions))))
    (wikimode--select-main-window)
    (let ((default-directory root))
      (call-interactively #'consult-ripgrep))))

(defun wikimode-return ()
  "Act on the thing at point.
Runs a search, expands a section, opens a file, or toggles a tag
filter, depending on what is under point."
  (interactive)
  (cond
   ((get-text-property (point) 'wikimode-search) (wikimode-search))
   ((get-text-property (point) 'wikimode-toggle) (wikimode-toggle-section))
   ((get-text-property (point) 'wikimode-file)
    (let ((file (expand-file-name (get-text-property (point) 'wikimode-file) wikimode--root)))
      (wikimode--select-main-window)
      (find-file file)))
   ((get-text-property (point) 'wikimode-tag)
    (let ((tag (get-text-property (point) 'wikimode-tag)))
      (setq wikimode--tag-filter (if (equal tag wikimode--tag-filter) nil tag))
      (wikimode--render)))
   (t (user-error "Nothing to do here"))))

(defun wikimode-mouse-return (event)
  "Move point to the clicked EVENT position and call `wikimode-return'."
  (interactive "e")
  (mouse-set-point event)
  (wikimode-return))

;;; Major mode

(defvar wikimode-mode-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map special-mode-map)
    (define-key map (kbd "RET") #'wikimode-return)
    (define-key map (kbd "<mouse-1>") #'wikimode-mouse-return)
    (define-key map (kbd "TAB") #'wikimode-toggle-section)
    (define-key map (kbd "/") #'wikimode-search)
    (define-key map (kbd "s") #'wikimode-cycle-file-sort)
    (define-key map (kbd "S") #'wikimode-cycle-tag-sort)
    (define-key map (kbd "a") #'wikimode-clear-tag-filter)
    (define-key map (kbd "f") #'wikimode-filter-section)
    (define-key map (kbd "F") #'wikimode-clear-section-filter)
    (define-key map (kbd "g") #'wikimode-refresh)
    (define-key map (kbd "n") #'next-line)
    (define-key map (kbd "p") #'previous-line)
    map)
  "Keymap for `wikimode-mode'.")

(defvar wikimode-mode-line-format
  '("%e" mode-line-frame-identification
    (:propertize "" face mode-line-buffer-id) "  "
    (:eval (and wikimode--root
                (file-name-nondirectory (directory-file-name wikimode--root))))
    "  " mode-line-end-spaces)
  "Simplified `mode-line-format' for `wikimode-mode'.")

(define-derived-mode wikimode-mode special-mode "Wiki"
  "Major mode for the wikimode side window.

A persistent side window for browsing a project of markdown or org
files the way a jekyll blog or github wiki presents itself: a full
text search entry point, a sortable file list, and a tag list parsed
from YAML frontmatter (markdown) or toplevel keywords (org). Selecting
a tag restricts the file list to files carrying that tag.

Key bindings:
  RET   open file at point / toggle tag filter / expand section / search
  TAB   expand or collapse the section at point
  /     full text search (via `consult-ripgrep') scoped to the project
  s     cycle file sort order (alphabetical / most recently modified)
  S     cycle tag sort order (alphabetical / by count)
  a     clear the active tag selection (which restricts the file list)
  f     filter the list at point (files by name/title, tags by name)
  F     clear the active filter for the section at point
  g     rescan the project for files and tags
  q     bury the window

\\{wikimode-mode-map}"
  (setq buffer-read-only t)
  (setq truncate-lines t)
  (setq-local mode-line-format wikimode-mode-line-format)
  (hl-line-mode 1))

;;; Window display

(defun wikimode--display-buffer (buffer alist)
  "Display BUFFER in a dedicated wikimode side window."
  (or (get-buffer-window buffer)
      (let ((window (display-buffer-in-side-window
                     buffer
                     (append alist
                             `((side . ,wikimode-position)
                               (slot . 0)
                               (window-width . ,wikimode-size)
                               (window-parameters . ((no-delete-other-windows . t))))))))
        (when window
          (set-window-dedicated-p window t))
        window)))

(defun wikimode--install-display-buffer ()
  (cl-pushnew `(,(concat "\\`" (regexp-quote wikimode-buffer-name) "\\'")
                wikimode--display-buffer)
              display-buffer-alist
              :test #'equal))

(wikimode--install-display-buffer)

(defun wikimode--get-buffer-create ()
  (or (get-buffer wikimode-buffer-name)
      (with-current-buffer (get-buffer-create wikimode-buffer-name)
        (wikimode-mode)
        (current-buffer))))

(defun wikimode--maybe-auto-refresh (&optional _arg)
  "Keep the visible wikimode window in sync with the selected window's buffer.
Rescans in place if the selected window has moved into a different
project than the one being shown; otherwise just updates which file
is highlighted as currently being viewed. Does nothing if the
wikimode window isn't shown, if the selected window is the wikimode
window itself or a minibuffer window (entering the minibuffer, e.g.
from `wikimode-filter-section' prompting for a filter, is not a
project switch and must not be treated as one), or if the selected
buffer isn't part of a recognized project (so switching to
scratch/help buffers doesn't blank it out).

Hooked to both `window-selection-change-functions' (switching windows)
and `window-buffer-change-functions' (switching buffers within a
window, e.g. via `switch-to-buffer' or a tab-line click) -- either
kind of switch can change which file should be highlighted, and
neither hook alone fires for both cases. Reads the selected window's
buffer explicitly rather than relying on the ambient current buffer,
since `window-buffer-change-functions' may run for a window other
than the selected one."
  (when-let ((window (get-buffer-window wikimode-buffer-name))
             (selected (selected-window)))
    (unless (or (eq selected window) (window-minibuffer-p selected))
      (let ((selected-buffer (window-buffer selected)))
        (when-let ((proj (with-current-buffer selected-buffer (project-current))))
          (let* ((root (project-root proj))
                 (buffer (window-buffer window))
                 (stale (not (equal (buffer-local-value 'wikimode--root buffer) root)))
                 (current (with-current-buffer selected-buffer
                            (wikimode--relative-current-file root))))
            (with-current-buffer buffer
              (if stale
                  (wikimode-refresh root)
                (unless (equal wikimode--current-file current)
                  (setq wikimode--current-file current)
                  (wikimode--render))))))))))

(add-hook 'window-selection-change-functions #'wikimode--maybe-auto-refresh)
(add-hook 'window-buffer-change-functions #'wikimode--maybe-auto-refresh)

;;;###autoload
(defun wikimode-toggle ()
  "Show or hide the wikimode side window.
Rescans automatically the first time it is shown, or whenever the
project it would show has changed since the last scan -- in that
case the window is refreshed in place rather than closed, even if
it was already visible."
  (interactive)
  (let* ((root (wikimode--find-root))
         (buffer (wikimode--get-buffer-create))
         (window (get-buffer-window buffer))
         (stale (not (equal (buffer-local-value 'wikimode--root buffer) root))))
    (if (and window (not stale))
        (delete-window window)
      (unless window
        (setq window (display-buffer buffer)))
      (with-current-buffer buffer
        (when stale
          (wikimode-refresh root)))
      (select-window window))))

(provide 'wikimode)
;;; wikimode.el ends here
